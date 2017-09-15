
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

    vector<vector<Aig_Obj_t*> > r0(numY), r1(numY);
    initializeRs(SAig, r0, r1);

    // Stop ABC
    Abc_Stop();
    return 0;
}
