#include <bits/stdc++.h>
#include <fstream>
#include <sstream>
using namespace std;

extern "C" {
#include "base/abc/abc.h"
#include "base/main/mainInt.h"
#include "base/cmd/cmd.h"
#include "base/abc/abc.h"
#include "misc/nm/nmInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "sat/bsat/satSolver2.h"
#include "opt/mfs/mfs.h"
#include "opt/mfs/mfsInt.h"
#include "bool/kit/kit.h"
Aig_Man_t * Abc_NtkToDar(Abc_Ntk_t * pNtk, int fExors, int fRegisters);
}

int CommandExecute(Abc_Frame_t* pAbc, string cmd);
vector<string> tokenize( const string& p_pcstStr, char delim );
string type2String(Aig_Type_t t);
void Equate(sat_solver *pSat, int varA, int varB);
void Xor(sat_solver *pSat, int varA, int varB);
Abc_Ntk_t* getNtk(string pFileName);
