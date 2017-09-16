
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
#include <bits/stdc++.h>
#include <fstream>
#include <sstream>
#include <ctime>
#include "helper.h"
#include "formula.h"

using namespace std;

// #define COMPARE_SAIGS // Uncomment to compare 2 SAigs
////////////////////////////////////////////////////////////////////////
///                           GLOBALS                                ///
////////////////////////////////////////////////////////////////////////

vector<int> varsXF, varsXS;
vector<int> varsYF, varsYS; // to be eliminated
int numOrigInputs, numX, numY;
Abc_Frame_t* pAbc;

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
void populateVars(Abc_Ntk_t* FNtk, AigToNNF& nnf, string varsFile,
                    vector<int>& varsXF, vector<int>& varsXS,
                    vector<int>& varsYF, vector<int>& varsYS,
                    map<string,int>& name2IdF, map<int,string>& id2NameF);
Aig_Obj_t* Aig_SubstituteConst(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, int one);
Aig_Obj_t* Aig_Substitute(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, Aig_Obj_t* func);
void initializeRs(Aig_Man_t* SAig,vector<vector<int> >& r0, vector<vector<int> >& r1);
Aig_Obj_t* buildF(Aig_Man_t* SAig);
Aig_Obj_t* buildFPrime(Aig_Man_t* SAig, const Aig_Obj_t* F_SAig);
void addVarToSolver(sat_solver* pSat, int varNum, int val);
int getCnfCoVarNum(Cnf_Dat_t* cnf, Aig_Man_t* aig, int nthCo);
lit addRlToSolver(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<int>& r);
lit addRlToSolver_rec(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<int>& r, int start, int end);
lit OR(sat_solver* pSat, lit lh, lit rh);
void addCnfToSolver(sat_solver* pSat, Cnf_Dat_t* cnf);

////////////////////////////////////////////////////////////////////////
///                         FUNCTIONS                                ///
////////////////////////////////////////////////////////////////////////

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
    Aig_Obj_t* currFI = Aig_ObjIsCo(initAig)? initAig->pFanin0: initAig;
    Aig_Obj_t* afterCompose = Aig_Compose(pMan, currFI, constf, varId-1);
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
    Aig_Obj_t* currFI = Aig_ObjIsCo(initAig)? initAig->pFanin0: initAig;
    Aig_Obj_t* afterCompose = Aig_Compose(pMan, currFI, func, varId-1);
    return afterCompose;
}

/** Function
 * Composes inputs of SAig with appropriate delta and gamma, makes the resulting
 * objects COs and stores them in r0 and r1.
 * @param SAig [in out]     Aig Manager
 * @param r0   [out]        Underapproximates the Cannot-be-0 sets
 * @param r1   [out]        Underapproximates the Cannot-be-1 sets
 */
void initializeRs(Aig_Man_t* SAig,
    vector<vector<int> >& r0, vector<vector<int> >& r1) {
    for(int i = 0; i < numY; ++i) {
        Aig_Obj_t* delta = Aig_ManCo(SAig, 0);
        for(int j = 0; j < numX; j++) {
            delta = Aig_Substitute(SAig, delta, varsXS[j], Aig_Not(Aig_ManCi(SAig, varsXS[j] - 1)));
        }
        for(int j = 0; j < numY; j++) {
            if(j < i)
                delta = Aig_SubstituteConst(SAig, delta, varsYS[j], 0);
            else if(j == i)
                delta = Aig_SubstituteConst(SAig, delta, varsYS[j], 1);
            else
                delta = Aig_Substitute(SAig, delta, varsYS[j], Aig_Not(Aig_ManCi(SAig, varsYS[j] - 1)));
        }
        for(int j = 0; j < numX; j++) {
            delta = Aig_Substitute(SAig, delta, numOrigInputs + varsXS[j], Aig_ManCi(SAig, varsXS[j] - 1));
        }
        for(int j = 0; j < numY; j++) {
            if(j <= i)
                delta = Aig_SubstituteConst(SAig, delta, numOrigInputs + varsYS[j], 0);
            else
                delta = Aig_Substitute(SAig, delta, numOrigInputs + varsYS[j], Aig_ManCi(SAig, varsYS[j] - 1));
        }
        // for(int j = numX + numY; j < 2*(numX + numY); j++)
            // Aig_ObjDelete(delta, Aig_ManCi(delta, j));
        Aig_ObjCreateCo(SAig, delta);
        r0[i].push_back(Aig_ManCoNum(SAig)-1);

        // reuse delta of the first half of the above for gamma
        Aig_Obj_t* gamma = Aig_ManCo(SAig, 0);
        for(int j = 0; j < numX; j++) {
            gamma = Aig_Substitute(SAig, gamma, varsXS[j], Aig_Not(Aig_ManCi(SAig, varsXS[j] - 1)));
        }
        for(int j = 0; j < numY; j++) {
            if(j <= i)
                gamma = Aig_SubstituteConst(SAig, gamma, varsYS[j], 0);
            else
                gamma = Aig_Substitute(SAig, gamma, varsYS[j], Aig_Not(Aig_ManCi(SAig, varsYS[j] - 1)));
        }
        for(int j = 0; j < numX; j++) {
            gamma = Aig_Substitute(SAig, gamma, numOrigInputs + varsXS[j], Aig_ManCi(SAig, varsXS[j] - 1));
        }
        for(int j = 0; j < numY; j++) {
            if(j < i)
                gamma = Aig_SubstituteConst(SAig, gamma, numOrigInputs + varsYS[j], 0);
            else if(j == i)
                gamma = Aig_SubstituteConst(SAig, gamma, numOrigInputs + varsYS[j], 1);
            else
                gamma = Aig_Substitute(SAig, gamma, numOrigInputs + varsYS[j], Aig_ManCi(SAig, varsYS[j] - 1));
        }
        // for(int j = numX + numY; j < 2*(numX + numY); j++)
            // Aig_ObjDelete(gamma, Aig_ManCi(gamma, j));
        Aig_ObjCreateCo(SAig, gamma);
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
    for(int i = 0; i < numX; ++i) {
        head = Aig_Substitute(SAig, head, varsXS[i], Aig_Not(Aig_ManObj(SAig, varsXS[i])));
    }
    for(int i = 0; i < numY; ++i) {
        head = Aig_Substitute(SAig, head, varsYS[i], Aig_Not(Aig_ManObj(SAig, varsYS[i])));
    }
    for(int i = 0; i < numX; ++i) {
        head = Aig_Substitute(SAig, head, varsXS[i] + numOrigInputs, Aig_ManObj(SAig, varsXS[i]));
    }
    for(int i = 0; i < numY; ++i) {
        head = Aig_Substitute(SAig, head, varsYS[i] + numOrigInputs, Aig_ManObj(SAig, varsYS[i]));
    }
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
    for(int i = 0; i < numY; ++i) {
        head = Aig_Substitute(SAig, head, varsYS[i], Aig_ManObj(SAig, varsYS[i] + numOrigInputs));
    }
    return Aig_ObjCreateCo(SAig, head);
}

/** Function
 * Asserts varNum to have value val
 * @param pSat      [in out]     Sat Solver
 * @param varNum    [in]         Variable number
 * @param val       [in]         Value to be assigned
 */
void addVarToSolver(sat_solver* pSat, int varNum, int val) {
    lit l = toLitCond(varNum, val==0);
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
 * @param pSat		[in]        Sat Solver
 * @param lh		[in]        lhs
 * @param rh		[in]        rhs
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
 * @param pSat		[in]        Sat Solver
 * @param cnf		[in]        Cnf Formula
 */
void addCnfToSolver(sat_solver* pSat, Cnf_Dat_t* cnf) {
	sat_solver_setnvars(pSat, sat_solver_nvars(pSat) + cnf->nVars);
    for (int i = 0; i < cnf->nClauses; i++)
        if (!sat_solver_addclause(pSat, cnf->pClauses[i], cnf->pClauses[i+1]))
            assert(false);
}

/** Function
 * Builds the ErrorFormula:
 * F(X,Y') and !F(X,Y) and \forall i (y_i == !r1[i])
 * @param pSat		[in]        Sat Solver
 * @param SAig		[in]        Aig to build the formula from
 */
void buildErrorFormula(sat_solver* pSat, Aig_Man_t* SAig,
    vector<vector<int> > &r0, vector<vector<int> > &r1) {
    Abc_Obj_t* pAbcObj;
    int i;

    // Build CNF
    Cnf_Dat_t* SCnf = Cnf_Derive(SAig, Aig_ManCoNum(SAig));
    addCnfToSolver(pSat, SCnf);

    #ifdef DEBUG_CHUNK
        Cnf_DataPrint(SCnf,1);

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
}

/** Function
 * Builds the ErrorFormula, Calls Sat Solver on it, populates cex.
 * Returns false if UNSAT.
 * F(X,Y') and !F(X,Y) and \forall i (y_i == !r1[i])
 * @param pSat		[in]		Sat Solver
 * @param SAig		[in]		Aig to build the formula from
 * @param cex		[out]		Counter-example, contains values of X Y neg_X neg_Y in order.
 */
bool callSATfindCEX(Aig_Man_t* SAig,vector<int>& cex,
    vector<vector<int> > &r0, vector<vector<int> > &r1) {
    OUT("callSATfindCEX..." );
    sat_solver *pSat = sat_solver_new();
    buildErrorFormula(pSat, SAig, r0, r1);

    OUT("Simplifying..." );
    if(!sat_solver_simplify(pSat)) {
        OUT("Formula is trivially unsat");
        return false;
    }
    else {
        OUT("Solving..." );
        int status = sat_solver_solve(pSat, 0, 0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);

        if (status == l_False) {
            OUT("Formula is unsat");
            return false;
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

            return true;
        }
    }
}

/** Function
 * This evaluates all nodes of the Aig using values from cex
 * The value of the node is stored in pObj->iData
 * @param formula	[in]		Aig Manager
 * @param cex		[in]		counter-example
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
 * @param formula	[in]		Aig Manager
 * @param cex 		[in]		Counterexample
 * @param coObjs	[in]		Co numbers in Aig Manager to check
 */
Aig_Obj_t* satisfiesVec(Aig_Man_t* formula, const vector<int>& cex, const vector<int>& coObjs) {
    evaluateAig(formula, cex);
    for(int i = 0; i < coObjs.size(); i++) {
        if(Aig_ManCo(formula,coObjs[i])->iData == 1) {
            return Aig_ManCo(formula,coObjs[i]);
        }
    }
    return NULL;
}

/** Function
 * Performs the function of the GENERALIZE routine as mentioned in FMCAD paper.
 * @param pMan		[in]		Aig Manager
 * @param cex		[in]		counter-example to be generalized
 * @param rl		[in]		Underaproximations of Cant-be sets
 */
static inline Aig_Obj_t* generalize(Aig_Man_t*pMan, vector<int> cex, const vector<int>& rl) {
	return satisfiesVec(pMan, cex, rl);
}

/** Function
 * Recursively checks if inpNodeId lies in support of root.
 * @param pMan		[in]		Aig Manager
 * @param root		[in]		Function to check support of
 * @param inpNodeId	[in]		ID of input variable to be checked
 * @param memo		[in]		A map for memoization
 */
bool Aig_Support_rec(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId, map<Aig_Obj_t*,bool>& memo) {
    if(root == NULL)
		return false;

    if(root->Id == inpNodeId)
        return true;

	if(memo.find(root) != memo.end())
		return memo[root];

    bool result = false;
    if(root->pFanin0 != NULL)
        result = result || Aig_Support_rec(pMan, root->pFanin0, inpNodeId, memo);
    if(root->pFanin1 != NULL)
        result = result || Aig_Support_rec(pMan, root->pFanin1, inpNodeId, memo);

    memo[root] = result;
    return result;
}

/** Function
 * Checks if inpNodeId lies in support of root.
 * @param pMan		[in]		Aig Manager
 * @param root		[in]		Function to check support of
 * @param inpNodeId	[in]		ID of input variable to be checked
 */
bool Aig_Support(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId) {
	map<Aig_Obj_t*,bool> memo;
	return Aig_Support_rec(pMan,root,inpNodeId,memo);
}

/** Function
 * Returns And of Aig1 and Aig2
 * @param pMan		[in]		Aig Manager
 * @param Aig1		[in]
 * @param Aig2		[in]
 */
Aig_Obj_t* Aig_AndAigs(Aig_Man_t* pMan, Aig_Obj_t* Aig1, Aig_Obj_t* Aig2) {
    Aig_Obj_t* lhs = Aig_ObjIsCo(Aig1)? Aig1->pFanin0: Aig1;
    Aig_Obj_t* rhs = Aig_ObjIsCo(Aig2)? Aig2->pFanin0: Aig2;
    return Aig_And(pMan, lhs, rhs);
}

/** Function
 * This updates r0 and r1 while eliminating cex
 * @param pMan		[in]		Aig Manager
 * @param r0		[in out]	Underaproximations of Cant-be-0 sets
 * @param r1		[in out]	Underaproximations of Cant-be-1 sets
 * @param cex		[in]		counter-example
 */
void updateAbsRef(Aig_Man_t* pMan, vector<vector<int> > &r0, vector<vector<int> > &r1,
    const vector<int> &cex) {

    int k, l, i;
    Aig_Obj_t *mu0, *mu1, *mu, *pAigObj;
    for(k = numY; k >= 0; k--) {
        if(((mu0 = satisfiesVec(pMan, cex, r0[k])) != NULL) &&
			((mu1 = satisfiesVec(pMan, cex, r1[k])) != NULL))
            break;
    }
    assert(k >= 0);
    // mu0 = generalize(pMan,cex, r0[k]);
    // mu1 = generalize(pMan,cex, r1[k]);
    mu = Aig_AndAigs(pMan, mu0, mu1);
    l = k + 1;

    OUT("Starting updateAbsRef Loop at at l = "<<l);
    while(true) {
		assert(l<numY);
		if(Aig_Support(pMan, mu, varsYS[l])) {
			if(cex[numX + l] == 1) {
				mu1 = Aig_SubstituteConst(pMan, mu, varsYS[l], 1);
				Aig_ObjCreateCo(pMan, mu1);
				r1[l].push_back(Aig_ManCoNum(pMan)-1);
				if(satisfiesVec(pMan, cex, r0[l]) != NULL) {
					mu0 = generalize(pMan,cex,r0[l]);
					mu = Aig_AndAigs(pMan, mu0, mu1);
				}
				else {
					break;
				}
			}
			else {
				mu0 = Aig_SubstituteConst(pMan, mu, varsYS[l], 0);
				Aig_ObjCreateCo(pMan, mu0);
				r0[l].push_back(Aig_ManCoNum(pMan)-1);
				mu1 = generalize(pMan,cex,r1[l]);
				mu = Aig_AndAigs(pMan, mu0, mu1);
			}
		}
		l = l+1;
    }
    return;
}

/** Function
 * Compresses Aig using the compressAig() routine
 * Deletes SAig and returns a compressed version
 * @param SAig		[in]		Aig to be compressed
 */
Aig_Man_t* compressAig(Aig_Man_t* SAig) {
	OUT("Cleaning up...");
	int removed = Aig_ManCleanup(SAig);
	OUT("Removed "<<removed<<" nodes");

	Aig_Man_t* temp = SAig;
	// Dar_ManCompress2( Aig_Man_t * pAig, int fBalance,
	// 					int fUpdateLevel, int fFanout,
	// 					int fPower, int fVerbose )
	OUT("Running Dar_ManCompress2...");
	SAig =  Dar_ManCompress2(SAig, 1, 1, 26, 1, 0);
	OUT("Stopping Old Aig Manager...");
	Aig_ManStop( temp );
	return SAig;
}

/** Function
 * Compresses Aig by converting it to an Ntk and performing a bunch of steps on it.
 * Deletes SAig and returns a compressed version
 * @param SAig		[in]		Aig to be compressed
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

////////////////////////////////////////////////////////////////////////
///                            MAIN                                  ///
////////////////////////////////////////////////////////////////////////
int main( int argc, char * argv[] )
{
	string pFileName, varsFile, benchmarkName;
	Abc_Obj_t* pAbcObj;
	Aig_Obj_t* pAigObj;
    map<string, int> name2IdF;
    map<int, string> id2NameF;
	int i, j;
    vector<int> cex;

	assert(argc >= 2);
    benchmarkName = string(argv[1]);
	pFileName     = benchmarkName;
	varsFile      = benchmarkName.substr(0,benchmarkName.find_last_of('.')) +
					((argc==2)?"_varstoelim.txt":string(argv[2]));

	clock_t main_start = clock();

    OUT("get FNtk..." );
    Abc_Ntk_t* FNtk = getNtk(pFileName,true);
    OUT("get FAig..." );
    Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);

    AigToNNF nnf(FAig);
    OUT("parse..." );
    nnf.parse();
    numOrigInputs = nnf.getNumInputs();
    OUT("process..." );
    nnf.process();
    OUT("createAig..." );
    nnf.createAig();
    OUT("getNtk..." );
    Abc_Ntk_t* SNtk = nnf.getNtk();
    Aig_Man_t* SAig = Abc_NtkToDar(SNtk, 0, 0);

    // #ifdef DEBUG_CHUNK // Print FAig, SAig
    //     // cout << "\nAig_ManPrintVerbose FAig: " << endl;
    //     // Aig_ManPrintVerbose(FAig,1);
    //     // cout << "\nAig_ManPrintVerbose SAig: " << endl;
    //     // Aig_ManPrintVerbose(SAig,1);
    //     cout << "\nFAig: " << endl;
    //     Abc_NtkForEachObj(FNtk,pAbcObj,i)
    //         cout <<"FAig Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

    //     cout << endl;
    //     Aig_ManForEachObj( FAig, pAigObj, i )
    //         Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );

    //     cout << "\nSAig: " << endl;
    //     Abc_NtkForEachObj(SNtk,pAbcObj,i)
    //         cout <<"SAig Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

    //     cout << endl;
    //     Aig_ManForEachObj( SAig, pAigObj, i )
    //         Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
    // #endif

    #ifdef COMPARE_SAIGS // Compare SAig1 to old SAig
        AigToNNF nnf2(pFileName);
        OUT("nnf2 parse..." );
        nnf2.parse();
        OUT("nnf2 process..." );
        nnf2.process();
        OUT("nnf2 resetCounters..." );
        nnf2.resetCounters();
        OUT("nnf2 createAig..." );
        nnf2.createAig();
        OUT("nnf2 getNtk..." );
        Abc_Ntk_t* SNtk2 = nnf2.getNtk();
        OUT("nnf2 get AIGs..." );
        Aig_Man_t* SAig2 = Abc_NtkToDar(SNtk2, 0, 0);

        cout << "Compare SAig1 to old SAig" << endl;
        cout << "#####################################################" << endl;
        cout << "\nSAig: " << endl;
        cout << "#####################################################" << endl;
        Abc_NtkForEachObj(SNtk,pAbcObj,i)
            cout <<"Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

        cout << endl;
        Aig_ManForEachObj( SAig, pAigObj, i )
            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );

        cout << "#####################################################" << endl;
        cout << "\nSAig2: " << endl;
        cout << "#####################################################" << endl;
        Abc_NtkForEachObj(SNtk2,pAbcObj,i)
            cout <<"Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

        cout << endl;
        Aig_ManForEachObj( SAig2, pAigObj, i )
            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );

        cout << "#####################################################" << endl;
        cout << "DONE!!!" << endl;
        cout << "#####################################################" << endl;
    #endif

    OUT("Aig_ManCoNum(SAig): " << Aig_ManCoNum(SAig));
    populateVars(FNtk, nnf, varsFile,
                    varsXF, varsXS,
                    varsYF, varsYS,
                    name2IdF, id2NameF);
	numX = varsXS.size();
	numY = varsYS.size();

    #ifdef DEBUG_CHUNK // Print nnf.inputs, varsXS, varsYS
        cout << "numX " << numX << endl;
        cout << "numY " << numY << endl;
        cout << "numOrigInputs " << numOrigInputs << endl;
        // cout << "varsXF: " << endl;
        // for(auto it : varsXF)
        //     cout << it << " ";
        // cout<<endl;
        // cout << "varsYF: " << endl;
        // for(auto it : varsYF)
        //     cout << it << " ";
        // cout<<endl;
        cout << "nnf.inputs: " << endl;
        for(auto it: nnf.inputs) {
            cout << it->var_num << " ";
        }
        cout << endl;

        cout << "varsXS: " << endl;
        for(auto it : varsXS)
            cout << it << " ";
        cout<<endl;
        cout << "varsYS: " << endl;
        for(auto it : varsYS)
            cout << it << " ";
        cout<<endl;
    #endif

    assert(numX + numY == numOrigInputs);

	// F_SAig      will always be Aig_ManCo( ... , 1)
	// FPrime_SAig will always be Aig_ManCo( ... , 2)
	cout << "buildF(SAig)..."<<endl;
	const Aig_Obj_t* F_SAig = buildF(SAig);
	cout << "buildFPrime(SAig)..."<<endl;
	const Aig_Obj_t* FPrime_SAig = buildFPrime(SAig, F_SAig);
    vector<vector<int> > r0(numY), r1(numY);
	cout << "initializeRs(SAig, r0, r1)..."<<endl;
	clock_t compose_start = clock();
    initializeRs(SAig, r0, r1);
	clock_t compose_end = clock();

	#ifdef DEBUG_CHUNK // Print SAig
        cout << "\nSAig: " << endl;
        Aig_ManForEachObj( SAig, pAigObj, i )
            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
    #endif
	cout << "Created SAig..." << endl;
	Aig_ManPrintStats( SAig );
	cout << "Compressing SAig..." << endl;
	SAig = compressAigByNtk(SAig);
	assert(SAig != NULL);
	Aig_ManPrintStats( SAig );
	#ifdef DEBUG_CHUNK // Print SAig
        cout << "\nSAig: " << endl;
        Aig_ManForEachObj( SAig, pAigObj, i )
            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
    #endif

    // CEGAR Loop
    cout << "Starting CEGAR Loop..."<<endl;
    int numloops = 0;
	while(callSATfindCEX(SAig, cex, r0, r1)) {
		OUT("\nIter " << numloops << ":\tFound CEX!");
		cout<<'.'<<flush;
		evaluateAig(SAig, cex);
		numloops++;

		if(numloops % 1000 == 0) {
			Aig_ManPrintStats( SAig );
			cout << "\nCompressing SAig..." << endl;
			SAig = compressAigByNtk(SAig);
			assert(SAig != NULL);
			Aig_ManPrintStats( SAig );
		}
	}

	cout << "Found Skolem Functions" << endl;
	cout << "Num Iterations: " << numloops << endl;

	clock_t main_end = clock();

    cout<< "Total time:   " <<double( main_end-main_start)/CLOCKS_PER_SEC << endl;
    cout<< "Compose time: " <<double( compose_end-compose_start)/CLOCKS_PER_SEC << endl;

    // Stop ABC
    Abc_Stop();
    return 0;
}
