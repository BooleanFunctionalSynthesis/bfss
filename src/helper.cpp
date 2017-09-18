#include "helper.h"
#include "formula.h"

////////////////////////////////////////////////////////////////////////
///                      HELPER FUNCTIONS                            ///
////////////////////////////////////////////////////////////////////////
int CommandExecute(Abc_Frame_t* pAbc, string cmd) {
	int ret = Cmd_CommandExecute(pAbc, (char*) cmd.c_str());
    if(ret) {
        cout << "Cannot execute command \""<<cmd<<"\".\n";
        return 1;
    }
    else
        return ret;
}

vector<string> tokenize( const string& p_pcstStr, char delim )  {
    vector<string> tokens;
    stringstream   mySstream( p_pcstStr );
    string         temp;
    while( getline( mySstream, temp, delim ) ) {
        if(temp!="")
        	tokens.push_back( temp );
    }
    return tokens;
}

string type2String(Aig_Type_t t) {
    switch(t) {
        case AIG_OBJ_NONE: return "AIG_OBJ_NONE";
        case AIG_OBJ_CONST1: return "AIG_OBJ_CONST1";
        case AIG_OBJ_CI: return "AIG_OBJ_CI";
        case AIG_OBJ_CO: return "AIG_OBJ_CO";
        case AIG_OBJ_BUF: return "AIG_OBJ_BUF";
        case AIG_OBJ_AND: return "AIG_OBJ_AND";
        case AIG_OBJ_EXOR: return "AIG_OBJ_EXOR";
    }
}

void Equate(sat_solver *pSat, int varA, int varB) {
    lit Lits[3];
    assert(varA!=0 && varB!=0);
    // cout << "Equate " << varA << " = " <<varB<<endl;
    // A -> B
    Lits[0] = toLitCond( abs(-varA), -varA<0 );
    Lits[1] = toLitCond( abs(varB), varB<0 );
    if(!sat_solver_addclause( pSat, Lits, Lits + 2 ))
        assert(false);

    // B -> A
    Lits[0] = toLitCond( abs(varA), varA<0 );
    Lits[1] = toLitCond( abs(-varB), -varB<0 );
    if(!sat_solver_addclause( pSat, Lits, Lits + 2 ))
        assert(false);
}

void Xor(sat_solver *pSat, int varA, int varB) {
    lit Lits[3];
    assert(varA!=0 && varB!=0);
    cout << "XOR " << varA << " ^ " <<varB<<endl;
    // A or B
    Lits[0] = toLitCond( abs(varA), varA<0 );
    Lits[1] = toLitCond( abs(varB), varB<0 );
    if(!sat_solver_addclause( pSat, Lits, Lits + 2 ))
        assert(false);

    // -A or -B
    Lits[0] = toLitCond( abs(-varA), -varA<0 );
    Lits[1] = toLitCond( abs(-varB), -varB<0 );
    if(!sat_solver_addclause( pSat, Lits, Lits + 2 ))
        assert(false);
}

Abc_Ntk_t*  getNtk(string pFileName, bool fraig) {
    string cmd, initCmd, varsFile, line;
    Abc_Obj_t* pPi, *pCi;
    set<int> varsX;
    set<int> varsY; // To Be Eliminated
    map<string, int> name2Id;
    int liftVal, cummulativeLift = 0;

    initCmd = "balance; rewrite -l; refactor -l; balance; rewrite -l; \
                        rewrite -lz; balance; refactor -lz; rewrite -lz; balance";

    pAbc = Abc_FrameGetGlobalFrame();

    cmd = "read " + pFileName;
    if (CommandExecute(pAbc, cmd)) { // Read the AIG
        return NULL;
    }
    cmd = fraig?initCmd:"balance";
    if (CommandExecute(pAbc, cmd)) { // Simplify
        return NULL;
    }
    // cmd = "print_stats";
    // if (CommandExecute(pAbc, cmd)) { // Stats
    //     return NULL;
    // }

    Abc_Ntk_t* pNtk =  Abc_FrameReadNtk (pAbc);
    // Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
    return pNtk;
}

/** Function
 * Reads the varsFile and populates essential maps and vectors using FNtk, nnf.
 * @param FNtk      [in]
 * @param nnf       [in]
 * @param varsFile  [in]
 * @param varsXF    [out]   maps x_i  to Id in FAig
 * @param varsXS    [out]   maps x_i  to Id in SAig
 * @param varsYF    [out]   maps y_i  to Id in FAig
 * @param varsYS    [out]   maps y_i  to Id in SAig
 * @param name2IdF  [out]   maps name to Id in FAig
 * @param Id2nameF  [out]   maps Id in FAig to name
 */
void populateVars(Abc_Ntk_t* FNtk, AigToNNF& nnf, string varsFile,
    vector<int>& varsXF, vector<int>& varsXS,
    vector<int>& varsYF, vector<int>& varsYS,
    map<string,int>& name2IdF, map<int,string>& id2NameF) {

    int i;
    Abc_Obj_t* pPi;
    string line;

    OUT( "Prim Inputs F:" );
    Abc_NtkForEachCi( FNtk, pPi, i ) {
        string variable_name = Abc_ObjName(pPi);
        name2IdF[variable_name] = pPi->Id;
        OUT( i << ": " << pPi->Id << ", " << variable_name );
    }
    for(auto it:name2IdF)
        id2NameF[it.second] = it.first;

    OUT( "Reading vars to elim..." );
    auto name2IdFTemp = name2IdF;
    ifstream varsStream(varsFile);
    if(!varsStream.is_open())
        cout << "Var File " + varsFile + " does not exist!" << endl;
    assert(varsStream.is_open());
    while (getline(varsStream, line)) {
        if(line != "") {
            auto it = name2IdFTemp.find(line);
            assert(it != name2IdFTemp.end());
            varsYF.push_back(it->second);
            name2IdFTemp.erase(it);
        }
    }
    for(auto it:name2IdFTemp) {
        varsXF.push_back(it.second);
    }

    OUT( "Populating varsXS varsYS..." );
    for(auto it : varsXF)
        varsXS.push_back(nnf.var_num2Id[it]);
    for(auto it : varsYF)
        varsYS.push_back(nnf.var_num2Id[it]);
}

/** Function
 * Composes input variable in initiAig with @param one, returns resulting Aig_Obj
 * @param pMan      [in out]    Aig Manager
 * @param initAig   [in]        Specifies the head of function tree
 * @param varId     [in]        (>=1) Specifies the variable to be substituted
 * @param one       [in]       set to 1 if varId is to be substituted by 1
 */
Aig_Obj_t* Aig_SubstituteConst(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, int one) {
    Aig_Obj_t* const1 = Aig_ManConst1(pMan);
    Aig_Obj_t* constf = (one? const1: Aig_Not(const1));
    Aig_Obj_t* currFI = Aig_ObjIsCo(Aig_Regular(initAig))? initAig->pFanin0: initAig;
    Aig_Obj_t* afterCompose = Aig_Compose(pMan, currFI, constf, varId-1);
    if(Aig_ObjIsCo(afterCompose))
        return Aig_ObjChild0(afterCompose);
    else
        return afterCompose;
}

/** Function
 * Composes input variable in initiAig with @param func, returns resulting Aig_Obj
 * @param pMan      [in out]    Aig Manager
 * @param initAig   [in]        Specifies the head of function tree
 * @param varId     [in]        (>=1) Specifies the variable to be substituted
 * @param func      [in]        Specifies the function that supplants the input
 */
Aig_Obj_t* Aig_Substitute(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, Aig_Obj_t* func) {
    Aig_Obj_t* currFI = Aig_ObjIsCo(Aig_Regular(initAig))? initAig->pFanin0: initAig;
    func = Aig_ObjIsCo(Aig_Regular(func))? func->pFanin0: func;
    Aig_Obj_t* afterCompose = Aig_Compose(pMan, currFI, func, varId-1);
    if(Aig_ObjIsCo(Aig_Regular(afterCompose))) {
        OUT(afterCompose);
        Aig_ObjPrintVerbose(Aig_Regular(afterCompose),1);
        cout << endl;
        assert(false);
        return Aig_ObjChild0(afterCompose);
    }
    else
        return afterCompose;
}

Aig_Obj_t* Aig_SubstituteVec(Aig_Man_t* pMan, Aig_Obj_t* initAig, vector<int>& varIdVec, 
    vector<Aig_Obj_t*>& funcVec) {
    Aig_Obj_t* currFI = Aig_ObjIsCo(Aig_Regular(initAig))? initAig->pFanin0: initAig;
    for (int i = 0; i < funcVec.size(); ++i) {
        funcVec[i] = Aig_ObjIsCo(Aig_Regular(funcVec[i]))? funcVec[i]->pFanin0: funcVec[i];
    }
    for (int i = 0; i < varIdVec.size(); ++i) {
        varIdVec[i]--;    
    }
    Aig_Obj_t* afterCompose = Aig_ComposeVec(pMan, currFI, funcVec, varIdVec);
    if(Aig_ObjIsCo(Aig_Regular(afterCompose))) {
        OUT(afterCompose);
        Aig_ObjPrintVerbose(Aig_Regular(afterCompose),1);
        cout << endl;
        assert(false);
        return Aig_ObjChild0(afterCompose);
    }
    else
        return afterCompose;
}

/** Function
 * Composes inputs of SAig with appropriate delta and gamma, makes the resulting
 * objects COs and stores them in r0 and r1.
 * @param SAig [in out]     Aig Manager
 * @param r0   [out]        Underapproximates the Cannot-be-0 sets
 * @param r1   [out]        Underapproximates the Cannot-be-1 sets
 */
void initializeR0(Aig_Man_t* SAig, vector<vector<int> >& r0) {
    for(int i = 0; i < numY; ++i) {
        vector<Aig_Obj_t* > funcVec;
        vector<int> varIdVec;
        Aig_Obj_t* delta = Aig_ManCo(SAig, 0);
        for(int j = 0; j < numX; j++) {
            funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsXS[j])));
            varIdVec.push_back(varsXS[j]);
        }
        for(int j = 0; j < numY; j++) {
            if(j < i) {
                funcVec.push_back(Aig_ManConst0(SAig));
                varIdVec.push_back(varsYS[j]);
            } else if(j == i) {
                funcVec.push_back(Aig_ManConst1(SAig));
                varIdVec.push_back(varsYS[j]);
            } else {
                funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsYS[j])));
                varIdVec.push_back(varsYS[j]);
            }
        }
        for(int j = 0; j < numX; j++) {
            funcVec.push_back(Aig_ManObj(SAig, varsXS[j]));
            varIdVec.push_back(numOrigInputs + varsXS[j]);
        }
        for(int j = 0; j < numY; j++) {
            if(j <= i) {
                funcVec.push_back(Aig_ManConst0(SAig));
                varIdVec.push_back(numOrigInputs + varsYS[j]);
            } else {
                funcVec.push_back(Aig_ManObj(SAig, varsYS[j]));
                varIdVec.push_back(numOrigInputs + varsYS[j]);
            }
        }
        delta = Aig_SubstituteVec(SAig, delta, varIdVec, funcVec);
        Aig_ObjCreateCo(SAig, delta);
        OUT("Pushing " << Aig_ManCoNum(SAig)-1 << " r0["<<i<<"]");
        r0[i].push_back(Aig_ManCoNum(SAig)-1);
    }
}

void initializeR1(Aig_Man_t* SAig, vector<vector<int> >& r1) {
    for(int i = 0; i < numY; ++i) {
        std::vector<Aig_Obj_t* > funcVec;
        std::vector<int> varIdVec;
        Aig_Obj_t* gamma = Aig_ManCo(SAig, 0);
        for(int j = 0; j < numX; j++) {
            funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsXS[j])));
            varIdVec.push_back(varsXS[j]);
        }
        for(int j = 0; j < numY; j++) {
            if(j <= i) {
                funcVec.push_back(Aig_ManConst0(SAig));
                varIdVec.push_back(varsYS[j]);
            } else {
                funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsYS[j])));
                varIdVec.push_back(varsYS[j]);
            }
        }
        for(int j = 0; j < numX; j++) {
            funcVec.push_back(Aig_ManObj(SAig, varsXS[j]));
            varIdVec.push_back(numOrigInputs + varsXS[j]);
        }
        for(int j = 0; j < numY; j++) {
            if(j < i) {
                funcVec.push_back(Aig_ManConst0(SAig));
                varIdVec.push_back(numOrigInputs + varsYS[j]);
            } else if(j == i) {
                funcVec.push_back(Aig_ManConst1(SAig));
                varIdVec.push_back(numOrigInputs + varsYS[j]);
            } else {
                funcVec.push_back(Aig_ManObj(SAig, varsYS[j]));
                varIdVec.push_back(numOrigInputs + varsYS[j]);
            }
        }
        gamma = Aig_SubstituteVec(SAig, gamma, varIdVec, funcVec);
        Aig_ObjCreateCo(SAig, gamma);
        OUT("Pushing " << Aig_ManCoNum(SAig)-1 << " r1["<<i<<"]");
        r1[i].push_back(Aig_ManCoNum(SAig)-1);
    }
}

/** Function
 * Returns a CO representing F; Composes SAig:
 * replaces x_neg inputs with not(x)
 * replaces y_neg inputs with not(y)
 * @param SAig [in out]     Aig Manager
 */
Aig_Obj_t* buildF(Aig_Man_t* SAig) {
    Aig_Obj_t* head = Aig_ManCo(SAig,0);
    vector<Aig_Obj_t* > funcVec;
    vector<int> iVarVec;
    for(int i = 0; i < numX; ++i) {
        funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsXS[i])));
        iVarVec.push_back(varsXS[i]);
    }
    for(int i = 0; i < numY; ++i) {
        funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsYS[i])));
        iVarVec.push_back(varsYS[i]);
    }
    for(int i = 0; i < numX; ++i) {
        funcVec.push_back(Aig_ManObj(SAig, varsXS[i]));
        iVarVec.push_back(varsXS[i] + numOrigInputs);
    }
    for(int i = 0; i < numY; ++i) {
        funcVec.push_back(Aig_ManObj(SAig, varsYS[i]));
        iVarVec.push_back(varsYS[i] + numOrigInputs);
    }
    head = Aig_SubstituteVec(SAig, head, iVarVec, funcVec);
    return Aig_ObjCreateCo(SAig, Aig_Not(head));
}

/** Function
 * Returns a CO representing F; Composes SAig:
 * replaces x_neg inputs with not(x)
 * replaces y     inputs with not(y_neg)
 * @param SAig [in out]     Aig Manager
 */
Aig_Obj_t* buildFPrime(Aig_Man_t* SAig, const Aig_Obj_t* F_SAig) {
    Aig_Obj_t* head = (Aig_Obj_t*) F_SAig;
    vector<Aig_Obj_t* > funcVec;
    vector<int> iVarVec;
    for(int i = 0; i < numY; ++i) {
        funcVec.push_back(Aig_ManObj(SAig, varsYS[i] + numOrigInputs));
        iVarVec.push_back(varsYS[i]);
    }
    head = Aig_SubstituteVec(SAig, head, iVarVec, funcVec);
    return Aig_ObjCreateCo(SAig, head);
}

/** Function
 * Asserts varNum to have value val
 * @param pSat      [in out]     Sat Solver
 * @param varNum    [in]         Variable number
 * @param val       [in]         Value to be assigned
 */
void addVarToSolver(sat_solver* pSat, int varNum, int val) {
    OUT("varNum: "<<varNum);
    OUT("val   : "<<val);
    OUT("val==0: "<<(val==0));
    lit l = toLitCond(varNum, (int)(val==0)?1:0);
    if(!sat_solver_addclause(pSat, &l, &l+1))
        assert(false);
}

/** Function
 * Returns variable number (in CNF) of specified Co
 * @param cnf       [in]        Cnf
 * @param aig       [in]        Aig
 * @param nthCo     [in]        Co
 */
int getCnfCoVarNum(Cnf_Dat_t* cnf, Aig_Man_t* aig, int nthCo) {
    return cnf->pVarNums[((Aig_Obj_t *)Vec_PtrEntry(aig->vCos, nthCo))->Id];
}

/** Function
 * Builds a balance OR-tree over elements in r, returns the head of the tree.
 * @param pSat      [in]        Sat Solver
 * @param GCnf      [in]        Cnf
 * @param GAig      [in]        Aig
 * @param r         [in]        vector of Co numbers
 */
lit addRlToSolver(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<int>& r) {

    // for(auto co:r)
    //     assert(Aig_ObjIsCo(co));

    return addRlToSolver_rec(pSat, GCnf, GAig, r, 0, r.size());
}

/** Function
 * Recursively Builds a balance OR-tree over elements r[start..end] and
 * returns the head of the tree.
 * @param pSat      [in out]    Sat Solver
 * @param GCnf      [in]        Cnf
 * @param GAig      [in]        Aig
 * @param r         [in]        vector of Aig_Obj_t*
 * @param start     [in]
 * @param end       [in]
 */
lit addRlToSolver_rec(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<int>& r, int start, int end) {

    assert(end > start);

    if(end == start+1)
        return GCnf->pVarNums[Aig_ManCo(GAig,r[start])->Id];

    int mid = (start+end)/2;
    lit lh = addRlToSolver_rec(pSat, GCnf, GAig, r, start, mid);
    lit rh = addRlToSolver_rec(pSat, GCnf, GAig, r, mid, end);
    lit nv = OR(pSat, lh, rh);

    return nv;
}

/** Function
 * Returns a new sat solver variable
 * @param pSat      [in]        Sat Solver
 * @param GCnf      [in]        Cnf
 * @param GAig      [in]        Aig
 * @param r         [in]        vector of Aig_Obj_t*
 */
int sat_solver_newvar(sat_solver* s) {
    // TODO use sat_solver_addvar
    sat_solver_setnvars(s, s->size+1);
    return s->size-1;
}

/** Function
 * Returns a new sat solver variable denoting OR of lh and rh
 * @param pSat      [in]        Sat Solver
 * @param lh        [in]        lhs
 * @param rh        [in]        rhs
 */
lit OR(sat_solver* pSat, lit lh, lit rh) {
    int nv = sat_solver_newvar(pSat);

    lit Lits[4];
    assert(lh!=0 && rh!=0);
    // nv -> lh or rh
    Lits[0] = toLitCond( abs(-nv), -nv<0 );
    Lits[1] = toLitCond( abs(lh), lh<0 );
    Lits[2] = toLitCond( abs(rh), rh<0 );
    if(!sat_solver_addclause( pSat, Lits, Lits + 3 ))
        assert(false);

    // lh -> nv
    Lits[0] = toLitCond( abs(-lh), -lh<0 );
    Lits[1] = toLitCond( abs(nv), nv<0 );
    if(!sat_solver_addclause( pSat, Lits, Lits + 2 ))
        assert(false);

    // rh -> nv
    Lits[0] = toLitCond( abs(-rh), -rh<0 );
    Lits[1] = toLitCond( abs(nv), nv<0 );
    if(!sat_solver_addclause( pSat, Lits, Lits + 2 ))
        assert(false);

    return nv;
}

/** Function
 * Adds CNF Formula to Solver
 * @param pSat      [in]        Sat Solver
 * @param cnf       [in]        Cnf Formula
 */
void addCnfToSolver(sat_solver* pSat, Cnf_Dat_t* cnf) {
    sat_solver_setnvars(pSat, sat_solver_nvars(pSat) + cnf->nVars);
    for (int i = 0; i < cnf->nClauses; i++)
        if (!sat_solver_addclause(pSat, cnf->pClauses[i], cnf->pClauses[i+1]))
            assert(false);
}

/** Function
 * Builds the ErrorFormula (see below) and returns SCnf.
 * F(X,Y') and !F(X,Y) and \forall i (y_i == !r1[i])
 * @param pSat      [in]        Sat Solver
 * @param SAig      [in]        Aig to build the formula from
 */
Cnf_Dat_t* buildErrorFormula(sat_solver* pSat, Aig_Man_t* SAig,
    vector<vector<int> > &r0, vector<vector<int> > &r1) {
    Abc_Obj_t* pAbcObj;
    int i;

    // Build CNF
    Cnf_Dat_t* SCnf = Cnf_Derive(SAig, Aig_ManCoNum(SAig));
    addCnfToSolver(pSat, SCnf);

    #ifdef DEBUG_CHUNK
        // Cnf_DataPrint(SCnf,1);

        // cout << "\nSAig: " << endl;
        // Abc_NtkForEachObj(SNtk,pAbcObj,i)
        //     cout <<"Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

        // cout << endl;
        // Aig_ManForEachObj( SAig, pAigObj, i )
        //     Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
        // cout << endl;

        // cout << "Original:    " << Aig_ManCo(SAig,0)->Id <<endl;
        // cout << "F_SAig:      " << Aig_ManCo(SAig,1)->Id <<endl;
        // cout << "FPrime_SAig: " << Aig_ManCo(SAig,2)->Id <<endl;
        // for(int i = 0; i < r1.size(); i++) {
        //     cout<<"r1[i]:       "<<Aig_ManCo(SAig,r1[i][0])->Id << endl;;
        // }
    #endif

    // assert F(X, Y) = false, F(X, Y') = true
    addVarToSolver(pSat, SCnf->pVarNums[Aig_ManCo(SAig,1)->Id], 0);
    addVarToSolver(pSat, SCnf->pVarNums[Aig_ManCo(SAig,2)->Id], 1);

    // Assert y_i == -r1[i]
    for (int i = 0; i < numY; ++i) {
        Equate(pSat, SCnf->pVarNums[varsYS[i]], -addRlToSolver(pSat, SCnf, SAig, r1[i]));
    }
    return SCnf;
}

/** Function
 * Builds the ErrorFormula, Calls Sat Solver on it, populates cex.
 * Returns false if UNSAT.
 * F(X,Y') and !F(X,Y) and \forall i (y_i == !r1[i])
 * @param pSat      [in]        Sat Solver
 * @param SAig      [in]        Aig to build the formula from
 * @param cex       [out]       Counter-example, contains values of X Y neg_X neg_Y in order.
 */
bool callSATfindCEX(Aig_Man_t* SAig,vector<int>& cex,
    vector<vector<int> > &r0, vector<vector<int> > &r1) {
    OUT("callSATfindCEX..." );
    bool return_val;
    sat_solver *pSat = sat_solver_new();
    Cnf_Dat_t *SCnf  = buildErrorFormula(pSat, SAig, r0, r1);

    OUT("Simplifying..." );
    if(!sat_solver_simplify(pSat)) {
        OUT("Formula is trivially unsat");
        return_val = false;
    }
    else {
        OUT("Solving..." );
        int status = sat_solver_solve(pSat, 0, 0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);

        if (status == l_False) {
            OUT("Formula is unsat");
            return_val = false;
        }
        else if (status == l_True) {
            OUT("Formula is sat; get the CEX");

            cex.resize(2*numOrigInputs);
            for (int i = 0; i < numX; ++i) {
                cex[i] = varsXS[i];
            }
            for (int i = 0; i < numY; ++i) {
                cex[numX + i] = varsYS[i];
            }
            for (int i = 0; i < numX; ++i) {
                cex[numOrigInputs + i] = varsXS[i] + numOrigInputs;
            }
            for (int i = 0; i < numY; ++i) {
                cex[numOrigInputs + numX + i] = varsYS[i] + numOrigInputs;
            }

            // for(auto e:cex)
            //     cout<<e<<endl;
            // cout<<endl<<endl;

            int * v = Sat_SolverGetModel(pSat, &cex[0], cex.size());
            cex = vector<int>(v,v+cex.size());

            #ifdef DEBUG_CHUNK
                for (int i = 0; i < cex.size(); ++i) {
                    cout<<i<<":\t"<<cex[i]<<endl;
                }
            #endif

            return_val = true;
        }
    }
    sat_solver_delete(pSat);
    Cnf_DataFree(SCnf);
    return return_val;
}

/** Function
 * This evaluates all nodes of the Aig using values from cex
 * The value of the node is stored in pObj->iData
 * @param formula   [in]        Aig Manager
 * @param cex       [in]        counter-example
 */
void evaluateAig(Aig_Man_t* formula, const vector<int> &cex) {
    // assert(cex.size() == Aig_ManCiNum(formula));
    int i;
    Aig_Obj_t* pObj;

    for (int i = 0; i < numX; ++i) {
        Aig_ManObj(formula, varsXS[i])->iData = cex[i];
    }
    for (int i = 0; i < numY; ++i) {
        Aig_ManObj(formula, varsYS[i])->iData = cex[numX + i];
    }
    for (int i = 0; i < numX; ++i) {
        Aig_ManObj(formula, varsXS[i]+numOrigInputs)->iData = cex[i+numOrigInputs];
    }
    for (int i = 0; i < numY; ++i) {
        Aig_ManObj(formula, varsYS[i]+numOrigInputs)->iData = cex[i+numX+numOrigInputs];
    }
    Aig_ManObj(formula,0)->iData = 1;

    Aig_ManForEachObj(formula, pObj, i) {
        // cout << "Evaluating node " << pObj->Id << endl;
        if(pObj->Id > 2*numOrigInputs) {
            pObj->iData = 1;
            int ld, rd;
            if(Aig_ObjFanin0(pObj) != NULL) {
                ld = Aig_ObjFanin0(pObj)->iData;
                if(Aig_IsComplement(pObj->pFanin0))
                    ld = 1 - ld;

                // cout << "\tld = " << ld << endl;
                pObj->iData *= ld;
            }
            if(Aig_ObjFanin1(pObj) != NULL) {
                rd = Aig_ObjFanin1(pObj)->iData;
                if(Aig_IsComplement(pObj->pFanin1))
                    rd = 1 - rd;

                // cout << "\trd = " << ld << endl;
                pObj->iData *= rd;
            }
        }
        // cout << "\tEvaluated node " << pObj->Id <<"\t= "<<pObj->iData<<endl;
    }
    return;
}

/** Function
 * Finds an element in coObjs that satisfies cex.
 * Returns the object, if found. Else, returns NULL.
 * Call evaluateAig(...) before this function.
 * @param formula   [in]        Aig Manager
 * @param cex       [in]        Counterexample
 * @param coObjs    [in]        Co numbers in Aig Manager to check
 */
Aig_Obj_t* satisfiesVec(Aig_Man_t* formula, const vector<int>& cex, const vector<int>& coObjs) {
    // evaluateAig(formula, cex);
    OUT("satisfiesVec...");
    for(int i = 0; i < coObjs.size(); i++) {
        OUT("Accessing Co "<<coObjs[i]<<" Id "<< Aig_ManCo(formula,coObjs[i])->Id);
        if(Aig_ManCo(formula,coObjs[i])->iData == 1) {
            OUT("Satisfied ID " << Aig_ManCo(formula,coObjs[i])->Id);
            return Aig_ManCo(formula,coObjs[i]);
        }
    }
    OUT("Nothing satisfied");
    return NULL;
}

/** Function
 * Performs the function of the GENERALIZE routine as mentioned in FMCAD paper.
 * @param pMan      [in]        Aig Manager
 * @param cex       [in]        counter-example to be generalized
 * @param rl        [in]        Underaproximations of Cant-be sets
 */
static inline Aig_Obj_t* generalize(Aig_Man_t*pMan, vector<int> cex, const vector<int>& rl) {
    return satisfiesVec(pMan, cex, rl);
}

/** Function
 * Recursively checks if inpNodeId lies in support of root.
 * @param pMan      [in]        Aig Manager
 * @param root      [in]        Function to check support of
 * @param inpNodeId [in]        ID of input variable to be checked
 * @param memo      [in]        A map for memoization
 */
bool Aig_Support_rec(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId, map<Aig_Obj_t*,bool>& memo) {
    if(root == NULL)
        return false;

    if(root->Id == inpNodeId)
        return true;

    if(Aig_ObjIsCi(root) || Aig_ObjIsConst1(root))
        return false;

    if(memo.find(root) != memo.end())
        return memo[root];

    bool result = false;
    if(Aig_ObjFanin0(root) != NULL)
        result = result || Aig_Support_rec(pMan, Aig_ObjFanin0(root), inpNodeId, memo);
    if(Aig_ObjFanin1(root) != NULL)
        result = result || Aig_Support_rec(pMan, Aig_ObjFanin1(root), inpNodeId, memo);

    memo[root] = result;
    return result;
}

/** Function
 * Checks if inpNodeId lies in support of root.
 * @param pMan      [in]        Aig Manager
 * @param root      [in]        Function to check support of
 * @param inpNodeId [in]        ID of input variable to be checked
 */
bool Aig_Support(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId) {
    map<Aig_Obj_t*,bool> memo;
    return Aig_Support_rec(pMan,Aig_Regular(root),inpNodeId,memo);
}

/** Function
 * Returns And of Aig1 and Aig2
 * @param pMan      [in]        Aig Manager
 * @param Aig1      [in]
 * @param Aig2      [in]
 */
Aig_Obj_t* Aig_AndAigs(Aig_Man_t* pMan, Aig_Obj_t* Aig1, Aig_Obj_t* Aig2) {
    Aig_Obj_t* lhs = Aig_ObjIsCo(Aig1)? Aig1->pFanin0: Aig1;
    Aig_Obj_t* rhs = Aig_ObjIsCo(Aig2)? Aig2->pFanin0: Aig2;
    return Aig_And(pMan, lhs, rhs);
}

/** Function
 * This updates r0 and r1 while eliminating cex
 * @param pMan      [in]        Aig Manager
 * @param r0        [in out]    Underaproximations of Cant-be-0 sets
 * @param r1        [in out]    Underaproximations of Cant-be-1 sets
 * @param cex       [in]        counter-example
 */
void updateAbsRef(Aig_Man_t* pMan, vector<vector<int> > &r0, vector<vector<int> > &r1,
    const vector<int> &cex) {

    for(auto it : cex)
        cout << it << " ";
    cout << endl;

    for (int i = 0; i < numX; ++i)
        cout << varsXS[i] << "\t" << cex[i] << endl;
    for (int i = 0; i < numY; ++i)
        cout << varsYS[i] << "\t" << cex[numX + i] << endl;
    for (int i = 0; i < numX; ++i)
        cout << numOrigInputs + varsXS[i] << "\t" << cex[numOrigInputs + i] << endl;
    for (int i = 0; i < numY; ++i)
        cout << numOrigInputs + varsYS[i] << "\t" << cex[numOrigInputs + numX + i] << endl;

    OUT("updateAbsRef...");
    int k, l, i;
    Aig_Obj_t *mu0, *mu1, *mu, *pAigObj;

    evaluateAig(pMan, cex);

    #ifdef DEBUG_CHUNK // Print SAig
        cout << "\nSAig: " << endl;
        Aig_ManForEachObj( pMan, pAigObj, i )
            Aig_ObjPrintVerbose( pAigObj, 1 ), cout<<"\t"<<pAigObj->iData, printf( "\n" );
    #endif

    OUT("Finding k...");
    for(k = numY-1; k >= 0; k--) {
        OUT("\nChecking k="<<k);
        if(((mu0 = satisfiesVec(pMan, cex, r0[k])) != NULL) &&
            ((mu1 = satisfiesVec(pMan, cex, r1[k])) != NULL))
            break;
    }
    assert(k >= 0);
    // mu0 = generalize(pMan,cex, r0[k]);
    // mu1 = generalize(pMan,cex, r1[k]);
    mu = Aig_AndAigs(pMan, mu0, mu1);
    l = k + 1;

    while(true) {
        OUT("Running updateAbsRef Loop at l = "<<l);
        assert(l<numY);
        if(Aig_Support(pMan, mu, varsYS[l])) {
            if(cex[numX + l] == 1) {
                mu1 = Aig_SubstituteConst(pMan, mu, varsYS[l], 1);
                Aig_ObjCreateCo(pMan, mu1);
                OUT("Pushing " << Aig_ManCoNum(pMan)-1 << " r1["<<l<<"]");
                r1[l].push_back(Aig_ManCoNum(pMan)-1);
                if(satisfiesVec(pMan, cex, r0[l]) != NULL) {
                    mu0 = generalize(pMan,cex,r0[l]);
                    mu = Aig_AndAigs(pMan, mu0, mu1);
                }
                else {
                    OUT("CEX Solved, breaking...");
                    break;
                }
            }
            else {
                mu0 = Aig_SubstituteConst(pMan, mu, varsYS[l], 0);
                Aig_ObjCreateCo(pMan, mu0);
                OUT("Pushing new node to r0["<<l<<"]...");
                r0[l].push_back(Aig_ManCoNum(pMan)-1);
                mu1 = generalize(pMan,cex,r1[l]);
                mu = Aig_AndAigs(pMan, mu0, mu1);
            }
        }
        l = l+1;
    }
    OUT("updateAbsRef done...");
    return;
}

/** Function
 * Compresses Aig using the compressAig() routine
 * Deletes SAig and returns a compressed version
 * @param SAig      [in]        Aig to be compressed
 */
Aig_Man_t* compressAig(Aig_Man_t* SAig) {
    OUT("Cleaning up...");
    int removed = Aig_ManCleanup(SAig);
    OUT("Removed "<<removed<<" nodes");

    Aig_Man_t* temp = SAig;
    // Dar_ManCompress2( Aig_Man_t * pAig, int fBalance,
    //                  int fUpdateLevel, int fFanout,
    //                  int fPower, int fVerbose )
    OUT("Running Dar_ManCompress2...");
    SAig =  Dar_ManCompress2(SAig, 1, 1, 26, 1, 0);
    OUT("Stopping Old Aig Manager...");
    Aig_ManStop( temp );
    return SAig;
}

/** Function
 * Compresses Aig by converting it to an Ntk and performing a bunch of steps on it.
 * Deletes SAig and returns a compressed version
 * @param SAig      [in]        Aig to be compressed
 */
Aig_Man_t* compressAigByNtk(Aig_Man_t* SAig) {
    Aig_Man_t* temp;
    string command;

    OUT("Cleaning up...");
    int removed = Aig_ManCleanup(SAig);
    OUT("Removed "<<removed<<" nodes");

    Abc_Ntk_t * SNtk = Abc_NtkFromAigPhase(SAig);
    Abc_FrameSetCurrentNetwork(pAbc, SNtk);
    // command = "rewrite -l; fraig;";
    command = "fraig; balance; rewrite -l; rewrite -lz; balance; rewrite -lz; \
                balance; rewrite -l; refactor -l; balance; rewrite -l; \
                rewrite -lz; balance; refactor -lz; rewrite -lz; balance;";
    if (Cmd_CommandExecute(pAbc, (char*)command.c_str())) {
        cout << "Cannot preprocess SNtk" << endl;
        return NULL;
    }
    SNtk = Abc_FrameReadNtk(pAbc);
    temp = Abc_NtkToDar(SNtk, 0, 0);
    Aig_ManStop(SAig);
    return temp;
}

/** Function
 * Checks and asserts expected support invariants for r0 r1 F_SAig and FPrime_Saig
 * @param SAig      [in]        Aig to be compressed
 * @param r0        [in]
 * @param r1        [in]
 */
void checkSupportSanity(Aig_Man_t*pMan, vector<vector<int> > &r0, vector<vector<int> > &r1) {
    for (int i = 0; i < numY; ++i) {
        for(auto co_num:r0[i])
            for (int j = 0; j <= i; ++j)
                assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsYS[j]) == false);
        for(auto co_num:r1[i])
            for (int j = 0; j <= i; ++j)
                assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsYS[j]) == false);
    }
    for (int i = 0; i < numY; ++i) {
        for(auto r:r0)
            for(auto co_num:r)
                assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsYS[i] + numOrigInputs) == false);
        for(auto r:r1)
            for(auto co_num:r)
                assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsYS[i] + numOrigInputs) == false);
    }
    for (int i = 0; i < numX; ++i) {
        for(auto r:r0)
            for(auto co_num:r)
                assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsXS[i] + numOrigInputs) == false);
        for(auto r:r1)
            for(auto co_num:r)
                assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsXS[i] + numOrigInputs) == false);
    }

    Aig_Obj_t* F_SAig = Aig_ManCo(pMan,1);
    Aig_Obj_t* FPrime_SAig = Aig_ManCo(pMan,2);

    for (int i = 0; i < numY; ++i) {
        assert(Aig_Support(pMan, F_SAig, varsYS[i] + numOrigInputs) == false);
        assert(Aig_Support(pMan, FPrime_SAig, varsYS[i]) == false);
    }
    for (int i = 0; i < numX; ++i) {
        assert(Aig_Support(pMan, F_SAig, varsXS[i] + numOrigInputs) == false);
        assert(Aig_Support(pMan, FPrime_SAig, varsXS[i] + numOrigInputs) == false);
    }
}

Aig_Obj_t* OR_rec(Aig_Man_t* SAig, vector<int>& nodes, int start, int end) {

    assert(end > start);

    if(end == start+1)
        return Aig_ObjChild0(Aig_ManCo(SAig,nodes[start]));

    int mid = (start+end)/2;
    Aig_Obj_t* lh = OR_rec(SAig, nodes, start, mid);
    Aig_Obj_t* rh = OR_rec(SAig, nodes, mid, end);
    Aig_Obj_t* nv = Aig_Or(SAig, lh, rh);

    return nv;
}

Aig_Obj_t* newOR(Aig_Man_t* SAig, vector<int>& nodes) {
    return OR_rec(SAig, nodes, 0, nodes.size());
}

void Aig_ObjDeleteCo( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    assert( Aig_ObjIsCo(pObj) );
    Aig_ObjDisconnect(p,pObj);
    // Aig_ObjDeref(Aig_ObjFanin0(pObj));
    pObj->pFanin0 = NULL;
    p->nObjs[pObj->Type]--;
    Vec_PtrWriteEntry( p->vObjs, pObj->Id, NULL );
    Aig_ManRecycleMemory( p, pObj );
    Vec_PtrRemove(p->vCos, pObj);
}

Aig_Obj_t* Aig_XOR(Aig_Man_t*p, Aig_Obj_t*p0, Aig_Obj_t*p1) {
    return Aig_Or( p, Aig_And(p, p0, Aig_Not(p1)), Aig_And(p, Aig_Not(p0), p1) );
}

bool verifyResult(Aig_Man_t* SAig, vector<vector<int> >& r0,
    vector<vector<int> >& r1, bool deleteCos) {
    int i; Aig_Obj_t*pAigObj;
    vector<int> r1Aigs(numY);

    OUT("compressAigByNtk...");
    SAig = compressAigByNtk(SAig);

    for(int i = 0; i < numY; i++) {
        OUT("Taking Ors..." << i);
        if(r1[i].size() == 1) {
            r1Aigs[i] = r1[i][0];
        }
        else {
            pAigObj = Aig_ObjCreateCo(SAig,newOR(SAig, r1[i]));
            r1Aigs[i] = Aig_ManCoNum(SAig)-1;
            assert(pAigObj!=NULL);
        }
    }

    if(deleteCos) {
        // Delete extra stuff
        set<int> requiredCOs;
        set<Aig_Obj_t*> redundantCos;
        for(auto it:r1Aigs)
            requiredCOs.insert(Aig_ManCo(SAig,it)->Id);
        requiredCOs.insert(Aig_ManCo(SAig,1)->Id);
        Aig_ManForEachCo( SAig, pAigObj, i) {
            if(requiredCOs.find(pAigObj->Id)==requiredCOs.end()) {
                redundantCos.insert(pAigObj);
            }
        }
        for(auto it:redundantCos) {
            Aig_ObjDeleteCo(SAig,it);
        }

        // Recompute r1Aigs
        vector<pair<int, int> > vv(numY);
        i = 0;
        for(auto it:r1Aigs)
            vv[i++] = make_pair(it,i);

        sort(vv.begin(), vv.end());
        i=1;
        for(auto it:vv) {
            r1Aigs[it.second] = i++;
        }
    }

    OUT("compressAigByNtk...");
    SAig = compressAigByNtk(SAig);

    #ifdef DEBUG_CHUNK // Print SAig, r1, r1Aigs
        cout << "\nSAig: " << endl;
        Aig_ManForEachObj( SAig, pAigObj, i )
            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
        i=0;
        for(auto it:r1) {
            cout<<"r1["<<i<<"] : ";
            for(auto it2:it)
                cout<<it2<<" ";
            cout<<endl;
            i++;
        }
        i=0;
        for(auto it:r1Aigs) {
            cout<<"r1Aigs["<<i<<"] : " << r1Aigs[i];
            i++;
        }
    #endif

    int i_temp;
    Aig_ManForEachObj(SAig,pAigObj,i_temp) {
        assert(Aig_ObjIsConst1(pAigObj) || Aig_ObjIsCi(pAigObj) || Aig_ObjIsCo(pAigObj) || (Aig_ObjFanin0(pAigObj) && Aig_ObjFanin1(pAigObj)));
    }

    OUT("Reverse Substitution...");
    for(int i = numY-2; i >= 0; --i) {
        OUT("i: " << i);
        Aig_Obj_t * curr = Aig_ManCo(SAig, r1Aigs[i]);
        if(i==3) {
            assert(true);
        }
        for(int j = i + 1; j < numY; ++j) {
            OUT("\tj: " << j);
            Aig_ManForEachObj(SAig,pAigObj,i_temp) {
                assert(Aig_ObjIsConst1(pAigObj) || Aig_ObjIsCi(pAigObj) || Aig_ObjIsCo(pAigObj) || (Aig_ObjFanin0(pAigObj) && Aig_ObjFanin1(pAigObj)));
            }

            OUT("\tCheck1:" << j);
            Aig_ManForEachCo(SAig,pAigObj,i_temp) {
                assert(pAigObj->nRefs == 0 && (pAigObj->pFanin1==NULL));
            }
            // if(i==3) {

            //     // #ifdef DEBUG_CHUNK // Print SAig
            //     //     cout << "\nSAig: " << endl;
            //     //     Aig_ManForEachObj( SAig, pAigObj, i )
            //     //         Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
            //     // #endif

            //     // OUT("Calling Substitute with args: ");
            //     // Aig_ObjPrintVerbose(curr,1);
            //     // OUT("");
            //     // OUT("node id: "<<varsYS[j]);
            //     // Aig_ObjPrintVerbose(Aig_ManCo(SAig,r1Aigs[j]),1);
            // }

            curr = Aig_Substitute(SAig, curr, varsYS[j], Aig_Not(Aig_ObjChild0(Aig_ManCo(SAig,r1Aigs[j]))));
            Aig_ObjPrintVerbose( Aig_Regular(curr), 1 ), printf( "\n" );
            assert(r1Aigs[i]!=NULL);
            assert(Aig_ObjIsCo(Aig_Regular(curr))==false);
            OUT("\tCheck2:" << j);
            Aig_ManForEachCo(SAig,pAigObj,i_temp) {
                assert(pAigObj->nRefs == 0 && (pAigObj->pFanin1==NULL));
            }

            // if(i == 3)
            // {
            //     #ifdef DEBUG_CHUNK // Print SAig
            //         cout << "\nSAig: " << endl;
            //         Aig_ManForEachObj( SAig, pAigObj, i )
            //             Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
            //     #endif
            // }

        }
        OUT("creating new CO...");
        Aig_ObjCreateCo(SAig,curr);
        r1Aigs[i] = Aig_ManCoNum(SAig)-1;
        assert(r1Aigs[i]!=NULL);
    }

    OUT("Final F Resubstitution...");
    Aig_Obj_t* F = Aig_ManCo(SAig, (deleteCos?0:1));
    for(int i = 0; i < numY; i++) {
        OUT("i: " << i);
        F = Aig_Substitute(SAig, F, varsYS[i], Aig_Not(Aig_ObjChild0(Aig_ManCo(SAig,r1Aigs[i]))));
    }
    OUT("F Id:     "<<Aig_Regular(F)->Id);
    OUT("F compl:  "<<Aig_IsComplement(F));
    OUT("Aig_ObjChild0(Aig_ManCo(SAig, (deleteCos?0:1))) Id:     "<<Aig_Regular(Aig_ObjChild0(Aig_ManCo(SAig, (deleteCos?0:1))))->Id);
    OUT("Aig_ObjChild0(Aig_ManCo(SAig, (deleteCos?0:1))) compl:  "<<Aig_IsComplement(Aig_ObjChild0(Aig_ManCo(SAig, (deleteCos?0:1)))));
    OUT("Aig_ObjChild0(Aig_ManCo(SAig, (deleteCos?0:1))):        "<<Aig_ObjChild0(Aig_ManCo(SAig, (deleteCos?0:1))));


    // F = Aig_Exor(SAig, F, Aig_ObjChild0(Aig_ManCo(SAig, (deleteCos?0:1))));
    // F = Aig_XOR(SAig, F, Aig_ObjChild0(Aig_ManCo(SAig, (deleteCos?0:1))));
    OUT("Aig_ManCoNum(SAig): "<<Aig_ManCoNum(SAig));

    cout<<F->Id<<endl;
    F = Aig_ObjCreateCo(SAig, F);
    OUT("Aig_ManCoNum(SAig): "<<Aig_ManCoNum(SAig));
    int F_num = Aig_ManCoNum(SAig)-1;


    #ifdef DEBUG_CHUNK // Print SAig
        cout << "\nSAig: " << endl;
        Aig_ManForEachObj( SAig, pAigObj, i )
            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
    #endif

    OUT("compressAigByNtk...");
    SAig = compressAigByNtk(SAig);

    sat_solver* pSat = sat_solver_new();
    Cnf_Dat_t* FCnf = Cnf_Derive(SAig, Aig_ManCoNum(SAig));
    addCnfToSolver(pSat, FCnf);
    // Cnf_DataPrint(FCnf,1);
    cout<<F_num<<endl;
    cout<<getCnfCoVarNum(FCnf, SAig, F_num)<<endl;
    // addVarToSolver(pSat, getCnfCoVarNum(FCnf, SAig, F_num), 0);
    // addVarToSolver(pSat, getCnfCoVarNum(FCnf, SAig, (deleteCos?0:1)), 1);
    lit LA[3];
    LA[0] = toLitCond(getCnfCoVarNum(FCnf, SAig, F_num),1);
    LA[1] = toLitCond(getCnfCoVarNum(FCnf, SAig, (deleteCos?0:1)),0);

    bool return_val;
    // int status = sat_solver_solve(pSat, 0, 0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
    int status = sat_solver_solve(pSat, LA, LA+2, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
    if (status == l_False) {
        OUT("Verified!");
        return_val = true;
    }
    else if (status == l_True) {
        OUT("Not Verified!");
        return_val = false;
    }
    sat_solver_delete(pSat);
    Cnf_DataFree(FCnf);
    return return_val;
}

void Aig_ComposeVec_rec( Aig_Man_t * p, Aig_Obj_t * pObj, vector<Aig_Obj_t *>& pFuncVec, 
    vector<Aig_Obj_t* >& iVarObjVec ) {
    assert( !Aig_IsComplement(pObj) );
    if ( Aig_ObjIsMarkA(pObj) )
        return;
    if ( Aig_ObjIsConst1(pObj) || Aig_ObjIsCi(pObj) ) {
        pObj->pData = pObj;
        int i = 0;
        for (auto iVarObj: iVarObjVec) {
            if(pObj == iVarObj) {
                pObj->pData = pFuncVec[i]; 
            }
            i++;
        }
        // pObj->pData = pFuncVec[idS[pObj->Id] - 1];
        return;
    }
    Aig_ComposeVec_rec( p, Aig_ObjFanin0(pObj), pFuncVec, iVarObjVec ); 
    Aig_ComposeVec_rec( p, Aig_ObjFanin1(pObj), pFuncVec, iVarObjVec );
    pObj->pData = Aig_And( p, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjSetMarkA( pObj );
}

Aig_Obj_t * Aig_ComposeVec( Aig_Man_t * p, Aig_Obj_t * pRoot, vector<Aig_Obj_t *>& pFuncVec, 
    vector<int>& iVarVec )
{
    // quit if the PI variable is not defined
    for(auto iVar: iVarVec) {
        if ( iVar >= Aig_ManCiNum(p) )
        {
            printf( "Aig_Compose(): The PI variable %d is not defined.\n", iVar );
            return NULL;
        }
    }
    // recursively perform composition
    vector<Aig_Obj_t *> iVarObjVec(iVarVec.size());
    int i = 0;
    for (auto iVar: iVarVec) {
        iVarObjVec[i++] = Aig_ManCi(p, iVar);
    }
    Aig_ComposeVec_rec( p, Aig_Regular(pRoot), pFuncVec, iVarObjVec );
    // clear the markings
    Aig_ConeUnmark_rec( Aig_Regular(pRoot) );
    return Aig_NotCond( (Aig_Obj_t *)Aig_Regular(pRoot)->pData, Aig_IsComplement(pRoot) );
}
