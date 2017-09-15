
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
#include <bits/stdc++.h>
#include <fstream>
#include <sstream>
#include "helper.h"
#include "formula.h"

using namespace std;

#define DEBUG
// #define COMPARE_SAIGS // Uncomment to compare 2 SAigs
#ifdef DEBUG
    #define OUT( x ) cout << x
#else
    #define OUT( x )
#endif
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
void initializeRs(Aig_Man_t* SAig,vector<vector<Aig_Obj_t*> >& r0, vector<vector<Aig_Obj_t*> >& r1);
Aig_Obj_t* buildF(Aig_Man_t* SAig);
Aig_Obj_t* buildFPrime(Aig_Man_t* SAig, const Aig_Obj_t* F_SAig);
void addVarToSolver(sat_solver* pSat, int varNum, int val);
int getCnfCoVarNum(Cnf_Dat_t* cnf, Aig_Man_t* aig, int nthCo);
lit addRlToSolver(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<Aig_Obj_t*>& r);
lit addRlToSolver_rec(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<Aig_Obj_t*>& r, int start, int end);
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

    OUT( "Prim Inputs F:" << endl);
    Abc_NtkForEachCi( FNtk, pPi, i ) {
        string variable_name = Abc_ObjName(pPi);
        name2IdF[variable_name] = pPi->Id;
        OUT( i << ": " << pPi->Id << ", " << variable_name << endl);
    }
    for(auto it:name2IdF)
        id2NameF[it.second] = it.first;

    OUT( "Reading vars to elim..." <<endl);
    auto name2IdFTemp = name2IdF;
    ifstream varsStream(varsFile);
    while (getline(varsStream, line)) {
        varsYF.push_back(name2IdFTemp[line]);
        name2IdFTemp.erase(line);
    }
    for(auto it:name2IdFTemp) {
        varsXF.push_back(it.second);
    }

    OUT( "Populating varsXS varsYS..." <<endl);
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
    vector<vector<Aig_Obj_t*> >& r0, vector<vector<Aig_Obj_t*> >& r1) {
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
        r0[i].push_back(Aig_ObjCreateCo(SAig, delta));

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
        r1[i].push_back(Aig_ObjCreateCo(SAig, gamma));
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
    OUT("addVarToSolver " << ((val)?(varNum):-varNum) << endl);
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
 * @param r         [in]        vector of Aig_Obj_t*
 */
lit addRlToSolver(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<Aig_Obj_t*>& r) {

    for(auto co:r)
        assert(Aig_ObjIsCo(co));

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
lit addRlToSolver_rec(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<Aig_Obj_t*>& r, int start, int end) {

    assert(end > start);

    if(end == start+1)
        return GCnf->pVarNums[r[start]->Id];

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

////////////////////////////////////////////////////////////////////////
///                            MAIN                                  ///
////////////////////////////////////////////////////////////////////////
int main( int argc, char * argv[] )
{
	string pFileName, cmd, initCmd, varsFile, line, benchmarkName;
    Abc_Obj_t* pPi, *pCi, *pAbcObj;
    Aig_Obj_t* pAigObj, *negVarObj;
    map<string, int> name2IdF;
    map<int, string> id2NameF;
    int i, j, liftVal, cummLiftF = 0, cummLiftS = 0;
    vector<int> cex;

    assert(argc == 2);
    benchmarkName = string(argv[1]);
    pFileName     = benchmarkName + ".v";
    varsFile      = benchmarkName + "_elimVars.txt";

    OUT("get FNtk..." <<endl);
    Abc_Ntk_t* FNtk = getNtk(pFileName);
    OUT("get FAig..." <<endl);
    Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);

    AigToNNF nnf(FAig);
    OUT("parse..." <<endl);
    nnf.parse();
    numOrigInputs = nnf.getNumInputs();
    OUT("process..." <<endl);
    nnf.process();
    OUT("createAig..." <<endl);
    nnf.createAig();
    OUT("getNtk..." <<endl);
    Abc_Ntk_t* SNtk = nnf.getNtk();
    Aig_Man_t* SAig = Abc_NtkToDar(SNtk, 0, 0);

    #ifdef DEBUG
        // cout << "\nAig_ManPrintVerbose FAig: " << endl;
        // Aig_ManPrintVerbose(FAig,1);
        // cout << "\nAig_ManPrintVerbose SAig: " << endl;
        // Aig_ManPrintVerbose(SAig,1);
        cout << "\nFAig: " << endl;
        Abc_NtkForEachObj(FNtk,pAbcObj,i)
            cout <<"Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

        cout << endl;
        Aig_ManForEachObj( FAig, pAigObj, i )
            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );

        cout << "\nSAig: " << endl;
        Abc_NtkForEachObj(SNtk,pAbcObj,i)
            cout <<"Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

        cout << endl;
        Aig_ManForEachObj( SAig, pAigObj, i )
            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
    #endif

    #ifdef COMPARE_SAIGS // Compare SAig1 to old SAig
        AigToNNF nnf2(pFileName);
        OUT("nnf2 parse..." <<endl);
        nnf2.parse();
        OUT("nnf2 process..." <<endl);
        nnf2.process();
        OUT("nnf2 resetCounters..." <<endl);
        nnf2.resetCounters();
        OUT("nnf2 createAig..." <<endl);
        nnf2.createAig();
        OUT("nnf2 getNtk..." <<endl);
        Abc_Ntk_t* SNtk2 = nnf2.getNtk();
        OUT("nnf2 get AIGs..." <<endl);
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

    OUT("Aig_ManCoNum(SAig): " << Aig_ManCoNum(SAig)<<endl);
    populateVars(FNtk, nnf, varsFile,
                    varsXF, varsXS,
                    varsYF, varsYS,
                    name2IdF, id2NameF);
    numX = varsXF.size();
    numY = varsYF.size();

    #ifdef DEBUG
        cout << "numX " << numX << endl;
        cout << "numY " << numY << endl;
        cout << "numOrigInputs " << numOrigInputs << endl;
        cout << "varsXF: " << endl;
        for(auto it : varsXF)
            cout << it << " ";
        cout<<endl;
        cout << "varsYF: " << endl;
        for(auto it : varsYF)
            cout << it << " ";
        cout<<endl;
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
	OUT("buildF(SAig)..."<<endl);
	const Aig_Obj_t* F_SAig = buildF(SAig);
	OUT("buildFPrime(SAig)..."<<endl);
	const Aig_Obj_t* FPrime_SAig = buildFPrime(SAig, F_SAig);
    vector<vector<Aig_Obj_t*> > r0(numY), r1(numY);
	OUT("initializeRs(SAig, r0, r1)..."<<endl);
    initializeRs(SAig, r0, r1);

	OUT("Instantiating new solver..." << endl);
	sat_solver *pSat = sat_solver_new();

	// Build CNF
	Cnf_Dat_t* SCnf = Cnf_Derive(SAig, Aig_ManCoNum(SAig));
	addCnfToSolver(pSat, SCnf);

	#ifdef DEBUG
		Cnf_DataPrint(SCnf,1);

		cout << "\nSAig: " << endl;
		Abc_NtkForEachObj(SNtk,pAbcObj,i)
			cout <<"Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

		cout << endl;
		Aig_ManForEachObj( SAig, pAigObj, i )
			Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
		cout << endl;

		cout << "Original:    " << Aig_ManCo(SAig,0)->Id <<endl;
		cout << "F_SAig:      " << F_SAig->Id <<endl;
		cout << "FPrime_SAig: " << FPrime_SAig->Id <<endl;
		for(int i = 0; i < r1.size(); i++) {
			cout<<"r1[i]:       "<<r1[i][0]->Id << endl;;
		}

	#endif

	// assert F(X, Y) = false, F(X, Y') = true
	addVarToSolver(pSat, SCnf->pVarNums[F_SAig->Id], 0);
	addVarToSolver(pSat, SCnf->pVarNums[FPrime_SAig->Id], 1);

	// Assert y_i == -r1[i]
	for (int i = 0; i < numY; ++i) {
		Equate(pSat, SCnf->pVarNums[varsYS[i]], -addRlToSolver(pSat, SCnf, SAig, r1[i]));
	}

	OUT("Simplifying..." << endl);
	if(!sat_solver_simplify(pSat)) {
		cout << "\nFormula is trivially unsat\n" << endl;
		return 0;
	}
	else {
		OUT("Solving..." << endl);
		int status = sat_solver_solve(pSat, 0, 0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);

		if (status == l_False) {
			cout << "\nFormula is unsat\n" << endl;
			return 0;
		}
		else if (status == l_True) {
			cout << "\nFormula is sat; get the CEX\n" << endl;
		}
	}

    // Stop ABC
    Abc_Stop();
    return 0;
}
