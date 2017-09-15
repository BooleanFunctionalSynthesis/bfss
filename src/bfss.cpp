
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


////////////////////////////////////////////////////////////////////////
///                         FUNCTIONS                                ///
////////////////////////////////////////////////////////////////////////

void populateVars(Abc_Ntk_t* FNtk, AigToNNF& nnf, string varsFile,
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

    populateVars(FNtk, nnf, varsFile, name2IdF, id2NameF);
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

    // Stop ABC
    Abc_Stop();
    return 0;
}
