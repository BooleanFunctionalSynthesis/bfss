#include "helper.h"

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

Abc_Ntk_t*  getNtk(string pFileName) {
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
    cmd = "balance";
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
