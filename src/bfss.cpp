
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
#include <bits/stdc++.h>
#include <fstream>
#include <sstream>
#include "helper.h"
#include "formula.h"

using namespace std;

// #define DEBUG

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
lit addRlToSolver(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<Aig_Obj_t*>& r);
lit addRlToSolver_rec(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<Aig_Obj_t*>& r, int start, int end);
lit OR(sat_solver* pSat, lit lh, lit rh);
void buildSatFormula(sat_solver* pSat, Aig_Man_t* FAig, Aig_Man_t* GAig, vector<vector<Aig_Obj_t*> > &r1);

void addCnfToSolver(sat_solver* pSat, Cnf_Dat_t* cnf);
int getCoVarNum(Cnf_Dat_t* cnf, Aig_Man_t* aig);
void addVarToSolver(sat_solver* pSat, int varNum, int neg);
void printMap(map<string,int> m);
static inline void evaluateAig(Aig_Man_t* formula, const vector<int> &cex);
bool satisfies(Aig_Man_t* formula, const vector<int> &cex, int coId);
Aig_Obj_t* satisfiesVec(Aig_Man_t* formula, const vector<int> &cex, vector<Aig_Obj_t* > coObjs);
Aig_Obj_t* generalize(Aig_Man_t* formula, const vector<int> &cex, vector<Aig_Obj_t* > coObjs);
Aig_Obj_t* Aig_AndAigs(Aig_Man_t* pMan, Aig_Obj_t* Aig1, Aig_Obj_t* Aig2);
Aig_Obj_t* Aig_SubstituteConst(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, int one);
Aig_Obj_t* Aig_Substitute(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, Aig_Obj_t* func);
void updateAbsRef(Aig_Man_t* pMan, vector<vector<Aig_Obj_t* > > &r0, vector<vector<Aig_Obj_t* > > &r1,
                    const vector<int> &cex);

////////////////////////////////////////////////////////////////////////
///                         FUNCTIONS                                ///
////////////////////////////////////////////////////////////////////////

lit addRlToSolver(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<Aig_Obj_t*>& r) {

    for(auto co:r)
        assert(Aig_ObjIsCo(co));

    return addRlToSolver_rec(pSat, GCnf, GAig, r, 0, r.size());
}

lit addRlToSolver_rec(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<Aig_Obj_t*>& r, int start, int end) {

    assert(end > start);

    if(end == start+1) {
        return GCnf->pVarNums[r[start]->Id];
    }

    int mid = (start+end)/2;
    lit lh = addRlToSolver_rec(pSat, GCnf, GAig, r, start, mid);
    lit rh = addRlToSolver_rec(pSat, GCnf, GAig, r, mid, end);
    lit nv = OR(pSat, lh, rh);

    return nv;
}

int sat_solver_newvar(sat_solver* s) {
    // TODO use sat_solver_addvar
    sat_solver_setnvars(s, s->size+1);
    return s->size-1;
}

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

void buildSatFormula(sat_solver* pSat, Aig_Man_t* FAig, Aig_Man_t* GAig, vector<vector<Aig_Obj_t*> > &r1) {
    int liftVal = 0;
    int cummLiftF = 0;

    sat_solver_setnvars(pSat, numX + 2*numY);

    cout << "Getting FCnf..." << endl;
    Cnf_Dat_t* FCnf = Cnf_Derive(FAig, 1);

    // Insert F(X, Y')
    liftVal = sat_solver_nvars(pSat) - cummLiftF;
    cummLiftF += liftVal;
    Cnf_DataLift(FCnf, liftVal);
    sat_solver_setnvars(pSat, sat_solver_nvars(pSat) + FCnf->nVars);
    addCnfToSolver(pSat, FCnf);

    // Assert F(X, Y') = true
    addVarToSolver(pSat, getCoVarNum(FCnf, FAig), 0);

    for (int i = 1; i <= numX; ++i) { // x_i-> x_i
        Equate(pSat, i, FCnf->pVarNums[varsXF[i-1]]);
    }
    for (int i = 1; i <= numY; ++i) { // y_i-> y_i'
        Equate(pSat, numX + numY + i, FCnf->pVarNums[varsYF[i-1]]);
    }

    // Insert F(X, Y)
    liftVal = sat_solver_nvars(pSat) - cummLiftF;
    cummLiftF += liftVal;
    Cnf_DataLift(FCnf, liftVal);
    sat_solver_setnvars(pSat, sat_solver_nvars(pSat) + FCnf->nVars);
    addCnfToSolver(pSat, FCnf);

    // Assert F(X, Y) = false
    addVarToSolver(pSat, getCoVarNum(FCnf, FAig), 1);

    for (int i = 1; i <= numX; ++i) { // x_i-> x_i
        Equate(pSat, i, FCnf->pVarNums[varsXF[i-1]]);
    }
    for (int i = 1; i <= numY; ++i) { // y_i-> y_i
        Equate(pSat, numX + i, FCnf->pVarNums[varsYF[i-1]]);
    }

    assert(numY == r1.size());

    cout << "Getting GCnf..." << endl;
    Cnf_Dat_t* GCnf = Cnf_Derive(GAig, Aig_ManCoNum(GAig));

    // Insert F(X, Y')
    liftVal = sat_solver_nvars(pSat);
    cummLiftF += liftVal;
    Cnf_DataLift(GCnf, liftVal);
    sat_solver_setnvars(pSat, sat_solver_nvars(pSat) + GCnf->nVars);
    addCnfToSolver(pSat, GCnf);

    for (int i = 1; i <= numX; ++i) { // x_i-> x_i
        Equate(pSat, i, GCnf->pVarNums[varsXF[i-1]]);
    }
    for (int i = 1; i <= numY; ++i) { // y_i-> y_i
        Equate(pSat, numX + i, GCnf->pVarNums[varsYF[i-1]]);
    }
    for(int i = 1; i <= numY; i++) { // y_i-> -r1[i]
        int r_var = addRlToSolver(pSat, GCnf, GAig, r1[i-1]);
        Equate(pSat, numX + i, -r_var);
    }
}

void addCnfToSolver(sat_solver* pSat, Cnf_Dat_t* cnf) {
    for (int i = 0; i < cnf->nClauses; i++)
        if (!sat_solver_addclause(pSat, cnf->pClauses[i], cnf->pClauses[i+1]))
            assert(false);
}

int getCoVarNum(Cnf_Dat_t* cnf, Aig_Man_t* aig) {
    return cnf->pVarNums[((Aig_Obj_t *)Vec_PtrEntry(aig->vCos, 0))->Id];
}

void addVarToSolver(sat_solver* pSat, int varNum, int neg) {
    cout << "addVarToSolver " << ((neg)?(-varNum):varNum) << endl;
    lit l = toLitCond(varNum, neg);
    if(!sat_solver_addclause(pSat, &l, &l+1))
        assert(false);
}

void printMap(map<string,int> m) {
    for(auto it:m) {
        cout<<it.first<<" "<<it.second<<endl;
    }
}

static inline void evaluateAig(Aig_Man_t* formula, const vector<int> &cex) {
    // assert(cex.size() == Aig_ManCiNum(formula));
    int i;
    Aig_Obj_t* pObj;
    Aig_ManForEachObj(formula, pObj, i) {
        // cout << "Evaluating node " << pObj->Id << endl;
        if(pObj->Id > 0) {
            if(i <= numX + numY) {
                // cout << "\tAssigned from cex" << endl;
                pObj->iData = cex[i-1];
            } else {
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
        }
        // cout << "\tEvaluated node " << pObj->Id <<"\t= "<<pObj->iData<<endl;
    }
    return;
}

bool satisfies(Aig_Man_t* formula, const vector<int> &cex, int coId) {
    evaluateAig(formula, cex);
    return Aig_ManCo(formula, coId)->iData;
}

Aig_Obj_t* satisfiesVec(Aig_Man_t* formula, const vector<int> &cex, vector<Aig_Obj_t* > coObjs) {
    evaluateAig(formula, cex);
    for(int i = 0; i < coObjs.size(); i++) {
        if(coObjs[i]->iData == 1) {
            return coObjs[i];
        }
    }
    return NULL;
}

Aig_Obj_t* generalize(Aig_Man_t* formula, const vector<int> &cex, vector<Aig_Obj_t* > coObjs) {
    Aig_Obj_t* temp = satisfiesVec(formula, cex, coObjs);
    assert(temp != NULL);
    return temp;
}

Aig_Obj_t* Aig_AndAigs(Aig_Man_t* pMan, Aig_Obj_t* Aig1, Aig_Obj_t* Aig2) {
    Aig_Obj_t* lhs = Aig_ObjIsCo(Aig1)? Aig1->pFanin0: Aig1;
    Aig_Obj_t* rhs = Aig_ObjIsCo(Aig2)? Aig2->pFanin0: Aig2;
    return Aig_And(pMan, lhs, rhs);
}

Aig_Obj_t* Aig_SubstituteConst(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, int one) {
    Aig_Obj_t* const1 = Aig_ManConst1(pMan);
    Aig_Obj_t* constf = (one? const1: Aig_Not(const1));
    Aig_Obj_t* currFI = Aig_ObjIsCo(initAig)? initAig->pFanin0: initAig;
    Aig_Obj_t* afterCompose = Aig_Compose(pMan, currFI, constf, varId-1);
    return afterCompose;
}

Aig_Obj_t* Aig_Substitute(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, Aig_Obj_t* func) {
    Aig_Obj_t* currFI = Aig_ObjIsCo(initAig)? initAig->pFanin0: initAig;
    Aig_Obj_t* afterCompose = Aig_Compose(pMan, currFI, func, varId-1);
    return afterCompose;
}

void updateAbsRef(Aig_Man_t* pMan, vector<vector<Aig_Obj_t* > > &r0, vector<vector<Aig_Obj_t* > > &r1,
    const vector<int> &cex) {

    int k, l, i;
    Aig_Obj_t *mu0, *mu1, *mu, *pAigObj;
    for(k = numY; k > 0; k--) {
        if(((mu0 = satisfiesVec(pMan, cex, r0[k - 1])) != NULL) &&
             ((mu1 = satisfiesVec(pMan, cex, r1[k - 1])) != NULL))
            break;
    }
    assert(k > 0);
    mu = Aig_AndAigs(pMan, mu0, mu1);
    l = k + 1;

    cout<<"Starting CEGAR Loop at at l = "<<l<<endl;
    while(true) {
        // if(Aig_ObjFanout0(mu, Aig_ManCi(mu, varsYF[l])) != NULL) {
            // Above condition assumes ith input have id i
            cout<<"l = "<<l<<endl;
            assert(l<=numY);
            if(cex[numX + l - 1]) {
                mu1 = Aig_SubstituteConst(pMan, mu, numX + l, 1);
                assert(!Aig_ObjIsCo(mu1));

                Aig_ObjPrint(pMan, mu1); cout << endl;
                Aig_ManForEachObj( pMan, pAigObj, i )
                    Aig_ObjPrint(pMan, pAigObj), cout << endl;


                cout<<"Updating r1 "<<l-1<<endl;

                // Aig_Obj_t* orObj = Aig_Or(pMan, r1[l-1][0]->pFanin0, mu1);
                // Aig_ObjPatchFanin0(pMan, r1[l-1][0], orObj);
                r1[l-1].push_back(Aig_ObjCreateCo(pMan, mu1));

                if(satisfiesVec(pMan, cex, r0[l-1]) != NULL) {
                    mu0 = generalize(pMan, cex, r0[l-1]);
                    mu = Aig_AndAigs(pMan, mu0, mu1);
                } else {
                    cout<<"CEX eliminated, Break!"<<endl;
                    break;
                }
            } else {
                mu0 = Aig_SubstituteConst(pMan, mu, numX + l, 0);
                assert(!Aig_ObjIsCo(mu0));
                Aig_ObjPrint(pMan, mu0); cout << endl;

                cout<<"Updating r0 "<<l-1<<endl;

                // Aig_Obj_t* orObj = Aig_Or(pMan, r0[l-1][0]->pFanin0, mu0);
                // Aig_ObjPatchFanin0(pMan, r0[l-1][0], orObj);
                r0[l-1].push_back(Aig_ObjCreateCo(pMan, mu0));
                mu1 = generalize(pMan, cex, r1[l-1]);
                mu = Aig_AndAigs(pMan, mu0, mu1);
            }
        // }
        l = l + 1;
    }
    return;
}


////////////////////////////////////////////////////////////////////////
///                            MAIN                                  ///
////////////////////////////////////////////////////////////////////////
int main( int argc, char * argv[] )
{
	string pFileName, cmd, initCmd, varsFile, line, benchmarkName;
    Abc_Obj_t* pPi, *pCi, *pAbcObj;
    Aig_Obj_t* pAigObj, *negVarObj;
    map<string, int> name2IdF, name2IdS;
    map<int, string> id2NameF, id2NameS;
    int i, j, liftVal, cummLiftF = 0, cummLiftS = 0;
    vector<int> cex;

    assert(argc == 2);
    benchmarkName = string(argv[1]);
	pFileName     = benchmarkName + ".v";
    varsFile      = benchmarkName + "_elimVars.txt";

    AigToNNF nnf(pFileName);
    cout << "parse..." <<endl;
    nnf.parse();
    numOrigInputs = nnf.getNumInputs();
    cout << "process..." <<endl;
    nnf.process();
    cout << "resetCounters..." <<endl;
    nnf.resetCounters();
    cout << "createAig..." <<endl;
    nnf.createAig();
    cout << "getNtk..." <<endl;
    Abc_Ntk_t* SNtk = nnf.getNtk();
    Abc_Ntk_t* FNtk = getNtk(pFileName);
    cout << "get AIGs..." <<endl;
    Aig_Man_t* SAig = Abc_NtkToDar(SNtk, 0, 0);
    Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);

    // Aig_ManPrintVerbose(FAig,1);
    cout << "\nFAig: " << endl;
    Abc_NtkForEachObj(FNtk,pAbcObj,i)
        cout <<"Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

    Aig_ManForEachObj( FAig, pAigObj, i )
        Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );

    cout << "\nSAig: " << endl;
    Abc_NtkForEachObj(SNtk,pAbcObj,i)
        cout <<"Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

    Aig_ManForEachObj( SAig, pAigObj, i )
        Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );

    // cout << "Prim Inputs F" << endl;
    // TODO Need to sort out
    for (int i = 0; (i < Abc_NtkPiNum(FNtk)) && (((pPi) = Abc_NtkPi(FNtk, i)), 1); i++ ) {
        string variable_name = Abc_ObjName(pPi);
        name2IdF[variable_name] = pPi->Id;
        // cout << i << ": " << pPi->Id << ", " << variable_name << endl;
    }
    // cout << "Prim Inputs S" << endl;
    for (int i = 0; (i < Abc_NtkPiNum(SNtk)) && (((pPi) = Abc_NtkPi(SNtk, i)), 1); i++ ) {
        string variable_name = Abc_ObjName(pPi);
        if(name2IdF.find(variable_name) != name2IdF.end()) {
            // cout << i << ": " << pPi->Id << ", " << variable_name << endl;
            name2IdS[variable_name] = pPi->Id;
        }
        else{
            // cout << i << ": " << pPi->Id << ", " << variable_name << endl;
            if(name2IdS.find(variable_name.substr(4,string::npos)) != name2IdS.end()) {
                // cout << "asserting " <<variable_name <<endl;
                assert(pPi->Id == numOrigInputs + name2IdS[variable_name.substr(4,string::npos)]);
            }
        }
    }
    for(auto it:name2IdS)
        id2NameS[it.second] = it.first;
    for(auto it:name2IdF)
        id2NameF[it.second] = it.first;

    // FOR DEBUGING
    // cout<<"name2IdF"<<endl;
    // printMap(name2IdF);
    // cout<<"name2IdS"<<endl;
    // printMap(name2IdS);

    cout << "Reading vars to elim..." <<endl;
    auto name2IdSTemp = name2IdS;
    auto name2IdFTemp = name2IdF;
    ifstream varsStream(varsFile);
    while (getline(varsStream, line)) {
        varsYF.push_back(name2IdFTemp[line]);
        varsYS.push_back(name2IdSTemp[line]);
        name2IdFTemp.erase(line);
        name2IdSTemp.erase(line);
    }
    for(auto it:name2IdSTemp) {
        varsXS.push_back(it.second);
    }
    for(auto it:name2IdFTemp) {
        varsXF.push_back(it.second);
    }
    name2IdSTemp.clear();
    name2IdFTemp.clear();
    numX = varsXF.size();
    numY = varsYF.size();
    assert(numX + numY == numOrigInputs);

    // TODO: Fix Aig_ManPrintVerbose!
    // Aig_ManPrintVerbose(SAig,1);
    // Aig_ManPrintVerbose(FAig,1);
    // Aig_ManDumpVerilog(FAig,"FAig.v");

    cout << "Instantiating new solver..." << endl;
    sat_solver *pSat = sat_solver_new();
    sat_solver_setnvars(pSat, numX + 2*numY);

    cout << "Getting FCnf..." << endl;
    Cnf_Dat_t* FCnf = Cnf_Derive(FAig, 1);
    cout << "nVars:     " << FCnf->nVars << endl;
    cout << "nLiterals: " << FCnf->nLiterals << endl;
    cout << "nClauses:  " << FCnf->nClauses << endl;

    // Insert F(X, Y')
    cout << "Insert F(X, Y')" << endl;
    liftVal = sat_solver_nvars(pSat) - cummLiftF;
    cummLiftF += liftVal;
    cout << "lifting to " << cummLiftF << endl;
    Cnf_DataLift(FCnf, liftVal);
    sat_solver_setnvars(pSat, sat_solver_nvars(pSat) + FCnf->nVars);
    addCnfToSolver(pSat, FCnf);

    #ifdef DEBUG
    Cnf_DataPrint(FCnf,1);
    for (int i = 1; i <= numX; ++i)
        cout << FCnf->pVarNums[varsXF[i-1]] << " : node " << varsXF[i-1]<<"("<<id2NameF[varsXF[i-1]]<<")" <<endl;
    for (int i = 1; i <= numY; ++i)
        cout << FCnf->pVarNums[varsYF[i-1]] << " : node " << varsYF[i-1]<<"("<<id2NameF[varsYF[i-1]]<<")" <<endl;
    #endif

    // Assert F(X, Y') = true
    cout << "Assert F(X, Y') = true" << endl;
    addVarToSolver(pSat, getCoVarNum(FCnf, FAig), 0);

    // FOR DEBUGING
    cout<<"\nvarsXF: ";
    for(auto it:varsXF)
        cout<<"  "<<it<<"("<<id2NameF[it]<<")";
    // cout<<"\nvarsXS: ";
    // for(auto it:varsXS)
    //     cout<<"  "<<it;
    cout<<"\nvarsYF: ";
    for(auto it:varsYF)
        cout<<"  "<<it<<"("<<id2NameF[it]<<")";
    // cout<<"\nvarsYS: ";
    // for(auto it:varsYS)
    //     cout<<"  "<<it;
    // cout<<"\nFCnf->pVarNums: ";
    // for (int i = 0; i <= 5; ++i)
    //     cout<<"  "<<FCnf->pVarNums[i];
    cout<<endl;

    for (int i = 1; i <= numX; ++i) { // x_i-> x_i
        Equate(pSat, i, FCnf->pVarNums[varsXF[i-1]]);
    }
    for (int i = 1; i <= numY; ++i) { // y_i-> y_i'
        Equate(pSat, numX + numY + i, FCnf->pVarNums[varsYF[i-1]]);
    }

    // Insert F(X, Y)
    cout << "Insert F(X, Y)" << endl;
    liftVal = sat_solver_nvars(pSat) - cummLiftF;
    cummLiftF += liftVal;
    cout << "lifting to " << cummLiftF << endl;
    Cnf_DataLift(FCnf, liftVal);
    sat_solver_setnvars(pSat, sat_solver_nvars(pSat) + FCnf->nVars);
    addCnfToSolver(pSat, FCnf);

    #ifdef DEBUG
    Cnf_DataPrint(FCnf,1);
    for (int i = 1; i <= numX; ++i)
        cout << FCnf->pVarNums[varsXF[i-1]] << " : node " << varsXF[i-1]<<"("<<id2NameF[varsXF[i-1]]<<")" <<endl;
    for (int i = 1; i <= numY; ++i)
        cout << FCnf->pVarNums[varsYF[i-1]] << " : node " << varsYF[i-1]<<"("<<id2NameF[varsYF[i-1]]<<")" <<endl;
    #endif


    // Assert F(X, Y) = false
    cout << "Assert F(X, Y) = false" << endl;
    addVarToSolver(pSat, getCoVarNum(FCnf, FAig), 1);

    for (int i = 1; i <= numX; ++i) { // x_i-> x_i
        Equate(pSat, i, FCnf->pVarNums[varsXF[i-1]]);
    }
    for (int i = 1; i <= numY; ++i) { // y_i-> y_i
        Equate(pSat, numX + i, FCnf->pVarNums[varsYF[i-1]]);
    }

    cout << "Getting SCnf..." << endl;
    Cnf_Dat_t* SCnf = Cnf_Derive(SAig, 1);
    cout << "nVars:     " << SCnf->nVars << endl;
    cout << "nLiterals: " << SCnf->nLiterals << endl;
    cout << "nClauses:  " << SCnf->nClauses << endl;
    cout << endl;

    for(int i = 1; i <= numY; ++i) {
        // Insert Gamma_i
        cout << "Insert Gamma_i" << endl;
        liftVal = sat_solver_nvars(pSat) - cummLiftS;
        cummLiftS += liftVal;
        cout << "lifting to " << cummLiftS << endl;
        Cnf_DataLift(SCnf,liftVal);
        sat_solver_setnvars(pSat, sat_solver_nvars(pSat) + SCnf->nVars);
        addCnfToSolver(pSat, SCnf);

        #ifdef DEBUG
        Cnf_DataPrint(SCnf,1);
        for (int i = 1; i <= numX; ++i)
            cout << SCnf->pVarNums[varsXS[i-1]] << " : node " << varsXS[i-1]<<"("<<id2NameF[varsXS[i-1]]<<")" <<endl;
        for (int i = 1; i <= numY; ++i)
            cout << SCnf->pVarNums[varsYS[i-1]] << " : node " << varsYS[i-1]<<"("<<id2NameF[varsYS[i-1]]<<")" <<endl;
        #endif

        // Assert y_i == -Gamma_i
        cout << "Assert y_i == -Gamma_i" << endl;
        int gVar = getCoVarNum(SCnf,SAig);
        // int gVar = SCnf->pVarNums[((Aig_Obj_t *)Vec_PtrEntry(SAig->vCos, 0))->Id];
        Equate(pSat, numX+i, -gVar);

        for (int j = 1; j <= numX; ++j) {
            cout << "Map x_j-> -x_j; neg_x_j-> x_j"<<endl;
            Equate(pSat, -j, SCnf->pVarNums[varsXS[j-1]]);
            Equate(pSat, j, SCnf->pVarNums[varsXS[j-1] + numX + numY]);
        }
        for (int j = 1; j <= numY; ++j) {
            if(j>i) {
                cout << "Map y_j-> -y_j; neg_y_j-> y_j"<<endl;
                Equate(pSat, -(numX + j),  SCnf->pVarNums[varsYS[j-1]]);
                Equate(pSat,  (numX + j), SCnf->pVarNums[varsYS[j-1] + numX + numY]);
            }
            else if(j<i) {
                cout << "Map y_j-> 0; neg_y_j-> 0"<<endl;
                addVarToSolver(pSat, SCnf->pVarNums[varsYS[j-1]], 1);
                addVarToSolver(pSat, SCnf->pVarNums[varsYS[j-1] + numX + numY], 1);
            }
            else {
                cout << "Map y_j-> 0; neg_y_j-> 1"<<endl;
                addVarToSolver(pSat, SCnf->pVarNums[varsYS[j-1]], 1);
                addVarToSolver(pSat, SCnf->pVarNums[varsYS[j-1] + numX + numY], 0);
            }
        }
    }

    Sat_SolverWriteDimacs(pSat,"solver.dimacs", 0, 0, 0);

    cout << "Solving..." << endl;
    // sat_solver_simplify();
    int status = sat_solver_solve(pSat, 0, 0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);

    if (status == l_False) {
        cout << "\nFormula is unsat\n";
    }
    else if (status == l_True) {
        cout << "\nFormula is sat; get the CEX\n";
        cex.resize(numOrigInputs+numY);
        iota(cex.begin(), cex.end(), 1);

        int * v = Sat_SolverGetModel(pSat, &cex[0], cex.size());
        cex = vector<int>(v,v+cex.size());

        for(int i=1;i<=numOrigInputs+numY;i++) {
            assert(sat_solver_var_value(pSat,i) == cex[i-1]);
        }

        // #ifdef DEBUG
        cout << "CEX: " << endl;
        for(int i=1;i<=numOrigInputs+numY;i++) {
            cout<<'\t'<<i;
        }
        cout<<endl;
        for(int i=1;i<=numOrigInputs+numY;i++) {
            cout<<'\t'<<cex[i-1];
        }
        cout<<endl;
        // #endif
    }
    else {
        cout << "\nNone\n";
        assert(false);
    }

    Sat_SolverWriteDimacs(pSat,"solver_simplied.dimacs", 0, 0, 0);


    vector<vector<Aig_Obj_t*> > r0(numY), r1(numY);
    cout << numY << endl;
    // r0.resize(numY);
    // r1.resize(numY);


    for(int i = 1; i <= numY; ++i) {
        Aig_Obj_t* delta = Aig_ManCo(SAig, 0);
        for(int j = 1; j <= numX; j++) {
            delta = Aig_Substitute(SAig, delta, j, Aig_Not(Aig_ManCi(SAig, j - 1)));
        }
        for(int j = 1; j <= numY; j++) {
            if(j < i)
                delta = Aig_SubstituteConst(SAig, delta, numX + j, 0);
            else if(j == i)
                delta = Aig_SubstituteConst(SAig, delta, numX + j, 1);
            else
                delta = Aig_Substitute(SAig, delta, numX + j, Aig_Not(Aig_ManCi(SAig, numX + j - 1)));
        }
        for(int j = 1; j <= numX; j++) {
            delta = Aig_Substitute(SAig, delta, numOrigInputs + j, Aig_ManCi(SAig, j - 1));
        }
        for(int j = 1; j <= numY; j++) {
            if(j <= i)
                delta = Aig_SubstituteConst(SAig, delta, numOrigInputs + numX + j, 0);
            else
                delta = Aig_Substitute(SAig, delta, numOrigInputs + numX + j, Aig_ManCi(SAig, numX + j - 1));
        }
        // for(int j = numX + numY; j < 2*(numX + numY); j++)
            // Aig_ObjDelete(delta, Aig_ManCi(delta, j));
        r0[i-1].push_back(Aig_ObjCreateCo(SAig, delta));

        // reuse delta of the first half of the above for gamma
        Aig_Obj_t* gamma = Aig_ManCo(SAig, 0);
        for(int j = 1; j <= numX; j++) {
            gamma = Aig_Substitute(SAig, gamma, j, Aig_Not(Aig_ManCi(SAig, j - 1)));
        }
        for(int j = 1; j <= numY; j++) {
            if(j <= i)
                gamma = Aig_SubstituteConst(SAig, gamma, numX + j, 0);
            else
                gamma = Aig_Substitute(SAig, gamma, numX + j, Aig_Not(Aig_ManCi(SAig, numX + j - 1)));
        }
        for(int j = 1; j <= numX; j++) {
            gamma = Aig_Substitute(SAig, gamma, numOrigInputs + j, Aig_ManCi(SAig, j - 1));
        }
        for(int j = 1; j <= numY; j++) {
            if(j < i)
                gamma = Aig_SubstituteConst(SAig, gamma, numOrigInputs + numX + j, 0);
            else if(j == i)
                gamma = Aig_SubstituteConst(SAig, gamma, numOrigInputs + numX + j, 1);
            else
                gamma = Aig_Substitute(SAig, gamma, numOrigInputs + numX + j, Aig_ManCi(SAig, numX + j - 1));
        }
        // for(int j = numX + numY; j < 2*(numX + numY); j++)
            // Aig_ObjDelete(gamma, Aig_ManCi(gamma, j));
        r1[i-1].push_back(Aig_ObjCreateCo(SAig, gamma));
    }


    // cout<<"composed SAig: (before deleting Po) "<<endl;
    // Aig_ManForEachObj( SAig, pAigObj, i )
    //     Aig_ObjPrintVerbose(pAigObj, 1), cout << endl;

    cout<<"numCos = "<<Aig_ManCoNum(SAig)<<endl;
    // Aig_ObjDisconnect(SAig,Aig_ManCo(SAig,0));
    cout<<"numCos = "<<Aig_ManCoNum(SAig)<<endl;
    // Aig_ObjDeletePo(SAig,Aig_ManCo(SAig,0));
    cout<<"numCos = "<<Aig_ManCoNum(SAig)<<endl;
    cout<<"composed SAig: (after deleting Po) "<<endl;
    Aig_ManForEachObj( SAig, pAigObj, i )
        Aig_ObjPrintVerbose(pAigObj, 1), cout << endl;

    cout<<"composed SAig: (after cleanup) "<<endl;
    Aig_ManCleanup(SAig);
    Aig_ManForEachObj( SAig, pAigObj, i )
        Aig_ObjPrintVerbose(pAigObj, 1), cout << endl;


    // Aig_ManSetCioIds(SAig);
    // Aig_ManCleanCioIds(SAig);

    cout<<"Deriving CNF..."<<endl;
    SCnf = Cnf_Derive(SAig,Aig_ManCoNum(SAig));
    cout<<"Derived CNF!!"<<endl;

    i = 0;
    for(auto roi:r0) {
        cout<<"R0["<<i++<<"] : ";
        cout<<roi[0]->Id<<endl;
    }
    i = 0;
    for(auto roi:r1) {
        cout<<"R1["<<i++<<"] : ";
        cout<<roi[0]->Id<<endl;
    }


    int loopCount = 0;
    while(status == l_True) {
        // CEGAR CALL
        cout << "LOOP COUNT : " << loopCount++ << endl;
        updateAbsRef(SAig, r0, r1, cex);

        cout << "SAig cleanup..." << endl;
        Aig_ManCleanup(SAig);
        cout<<"SAig: (after cleanup) "<<endl;
        Aig_ManForEachObj( SAig, pAigObj, i )
            Aig_ObjPrintVerbose(pAigObj, 1), cout << endl;

        cout << "Instantiating new solver..." << endl;
        sat_solver *pSat = sat_solver_new();


        cout << "building SatFormula..." << endl;
        buildSatFormula(pSat, FAig, SAig, r1);
        Sat_SolverWriteDimacs(pSat,"solver.dimacs", 0, 0, 0);

        cout << "Solving..." << endl;
        // sat_solver_simplify();
        int status = sat_solver_solve(pSat, 0, 0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);

        if (status == l_False) {
            cout << "\nFormula is unsat\n";
            break;
        }
        else if (status == l_True) {
            cout << "\nFormula is sat; get the CEX\n";
            cex.resize(numOrigInputs+numY);
            iota(cex.begin(), cex.end(), 1);

            int * v = Sat_SolverGetModel(pSat, &cex[0], cex.size());
            cex = vector<int>(v,v+cex.size());

            for(int i=1;i<=numOrigInputs+numY;i++) {
                assert(sat_solver_var_value(pSat,i) == cex[i-1]);
            }

            #ifdef DEBUG
            cout << "CEX: " << endl;
            for(int i=1;i<=numOrigInputs+numY;i++) {
                cout<<'\t'<<i;
            }
            cout<<endl;
            for(int i=1;i<=numOrigInputs+numY;i++) {
                cout<<'\t'<<cex[i-1];
            }
            cout<<endl;
            #endif
        }
        else {
            cout << "\nNone\n";
            assert(false);
        }
        Sat_SolverWriteDimacs(pSat,"solver_simplied.dimacs", 0, 0, 0);
    }

    // Stop ABC
    Abc_Stop();
    return 0;
}
