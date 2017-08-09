
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

Abc_Frame_t* pAbc;

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

// bool satisfies(const vector<int> &cex, Aig_Man_t* formula) {
//     // TODO

//     // Aig_Man_t* dupFormula = Aig_ManDupSimple(formula);
//     // for(int i = 0; i < cex.size(); i++) {

//     // }
//     // Aig_Obj_t* input;
//     // int i; 
//     // Aig_ManForEachCi(dupFormula, input, i) {


//     // }
// }

// int satisfiesVec(const vector<int> &cex, vector<Aig_Man_t* > formula) {
//     for(int i = 0; i < formula.size(); i++) {
//         if(satisfies(cex, formula[i])) {
//             return i;
//         }
//     }
//     return -1;
// }

// Aig_Man_t* generalize(const vector<int> &cex, vector<Aig_Man_t*> r0l) {
//     Aig_Man_t* genResult;
//     for(int i = 0; i < r0l.size(); i++) {
//         if(satisfies(cex, r0l[i])) {
//             genResult = r0l[i];
//             return genResult; 
//         }
//     }
// }

// Aig_Man_t* Aig_AndAigs(Aig_Man_t* lhs, Aig_Man_t* rhs) {
//     // TODO
//     // rhs can be added to lhs

// }

// Aig_Man_t* Aig_Substitute(Aig_Man_t* initAig, int varId, int one) {
//     Aig_Obj_t* currCo = Aig_ManCo(initAig, 0);
//     Aig_Obj_t* const1 = Aig_ManConst1(initAig);
//     Aig_Obj_t* constf = (one? const1: Aig_Not(const1));
//     Aig_Obj_t* currFI = Aig_ObjFanin0(currCo);;
//     Aig_Obj_t* afterCompose = Aig_Compose(initAig, currFI, constf, varId);
//     // check var id in the above compose
//     Aig_ObjPatchFanin0(initAig, currCo, afterCompose);
//     return initAig;
// }

// void updateAbsRef(vector<vector<Aig_Man_t* > > &r0, vector<vector<Aig_Man_t* > > &r1, 
//                     const vector<int> &cex) {
    
//     int k, l, mu0Index = -1, mu1Index = -1;
//     for(k = numY; k > 0; k--) {
//         if(((mu0Index = satisfiesVec(cex, r0[k - 1])) != -1) &&
//              ((mu1Index = satisfiesVec(cex, r1[k - 1])) != -1)) 
//             break;
//     }
//     assert(k != 0);
//     l = k + 1;

//     Aig_Man_t* mu0, mu1;
//     mu0 = generalize(cex, r0[k]);
//     mu1 = generalize(cex, r1[k]);
//     mu = Aig_AndAigs(mu0, mu1);

//     while(true) {
//         if(Aig_ObjFanout0(mu, Aig_ManCi(mu, varsYF[l])) != NULL) {
//             // Above condition assumes ith input have id i
//             if(cex[numX + l - 1]) {
//                 mu1 = Aig_Substitute(mu, numX + l, 1);
//                 r1[l].push_back(mu1);
//                 if(satisfiesVec(cex, r0[l]) != -1) { 
//                     mu0 = generalize(cex, r0[l]);
//                     mu = Aig_AndAigs(mu0, mu1);
//                 } else {
//                     break;
//                 }
//             } else {
//                 mu0 = Aig_Substitute(mu, numX + l, 0);
//                 r0[l].push_back(mu0);
//                 mu1 = generalize(cex, r1[l]);
//                 mu = Aig_AndAigs(mu0, mu1);
//             }
//         }
//         l = l + 1;
//     }
//     return;
// }



////////////////////////////////////////////////////////////////////////
///                            MAIN                                  ///
////////////////////////////////////////////////////////////////////////
int main( int argc, char * argv[] )
{
	string pFileName, cmd, initCmd, varsFile, line, benchmarkName;
    Abc_Obj_t* pPi, *pCi, *pAbcObj;
    Aig_Obj_t* pAigObj, *negVarObj;
    vector<int> varsXF, varsXS;
    vector<int> varsYF, varsYS; // to be eliminated
    map<string, int> name2IdF, name2IdS;
    map<int, string> id2NameF, id2NameS;
    int i, j, liftVal, cummLiftF = 0, cummLiftS = 0, numOrigInputs, numX, numY;

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

    if (status == l_False)
        cout << "\nFormula is unsat\n";
    else if (status == l_True) {
        cout << "\nFormula is sat; get the CEX\n";
        vector<int> cex(numOrigInputs+numY);
        iota(cex.begin(), cex.end(), 1);

        int * v = Sat_SolverGetModel(pSat, &cex[0], cex.size());
        cex = vector<int>(v,v+cex.size());

        for(int i=1;i<=numOrigInputs+numY;i++) {
            assert(sat_solver_var_value(pSat,i) == cex[i-1]);
        }

        #ifdef DEBUG
        cout << "CEX: 0" << endl;
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
    }

    Sat_SolverWriteDimacs(pSat,"solver_simplied.dimacs", 0, 0, 0);




    // Stop ABC
    Abc_Stop();
    return 0;
}
