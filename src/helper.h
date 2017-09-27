#include <bits/stdc++.h>
#include <fstream>
#include <sstream>
#include <stack>
using namespace std;

extern "C" {
#include "base/abc/abc.h"
#include "base/main/mainInt.h"
#include "base/cmd/cmd.h"
#include "base/abc/abc.h"
#include "misc/nm/nmInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "sat/bsat/satSolver.h"
#include "sat/bsat/satSolver2.h"
#include "opt/mfs/mfs.h"
#include "opt/mfs/mfsInt.h"
#include "bool/kit/kit.h"
Aig_Man_t * Abc_NtkToDar(Abc_Ntk_t * pNtk, int fExors, int fRegisters);
Abc_Ntk_t * Abc_NtkFromAigPhase(Aig_Man_t * pMan);
}

#define UNIGEN_OUT_DIR		"out"
#define UNIGEN_INPUT_FNAME 	"errorFormula"
#define UNIGEN_OUTPT_FNAME	"unigen_output.txt"
#define UNIGEN_DIMAC_FNAME 	UNIGEN_INPUT_FNAME ".cnf"
#define UNIGEN_MODEL_FNAME	UNIGEN_INPUT_FNAME ".txt"
#define UNIGEN_OUTPT_FPATH	UNIGEN_OUTPT_FNAME
#define UNIGEN_MODEL_FPATH	UNIGEN_OUT_DIR "/" UNIGEN_MODEL_FNAME
#define UNIGEN_DIMAC_FPATH 	UNIGEN_DIMAC_FNAME
#define UNIGEN_PY 			"UniGen2.py"
#define UNIGEN_SAMPLES		22

// #define DEBUG
// #define DEBUG_CHUNK
// #define COMPARE_SAIGS // Uncomment to compare 2 SAigs
#ifdef DEBUG
	#define OUT( x ) cout << "DEBUG: " << x << endl
#else
	#define OUT( x )
#endif

extern vector<int> varsSInv;
extern vector<int> varsXF, varsXS;
extern vector<int> varsYF, varsYS; // to be eliminated
extern int numOrigInputs, numX, numY;
extern Abc_Frame_t* pAbc;

class edge;
class node;
class AigToNNF;

int 			CommandExecute(Abc_Frame_t* pAbc, string cmd);
vector<string> 	tokenize( const string& p_pcstStr, char delim );
string 			type2String(Aig_Type_t t);
void 			Equate(sat_solver *pSat, int varA, int varB);
void 			Xor(sat_solver *pSat, int varA, int varB);
Abc_Ntk_t* 		getNtk(string pFileName, bool fraig);
void 			populateVars(Abc_Ntk_t* FNtk, AigToNNF& nnf, string varsFile,
					vector<int>& varsXF, vector<int>& varsXS,
					vector<int>& varsYF, vector<int>& varsYS,
					map<string,int>& name2IdF, map<int,string>& id2NameF);
Aig_Obj_t* 		Aig_SubstituteConst(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, int one);
Aig_Obj_t* 		Aig_Substitute(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, Aig_Obj_t* func);
void 			initializeR0(Aig_Man_t* SAig,vector<vector<int> >& r0);
void 			initializeR1(Aig_Man_t* SAig,vector<vector<int> >& r1);
Aig_Obj_t* 		buildF(Aig_Man_t* SAig);
Aig_Obj_t* 		buildFPrime(Aig_Man_t* SAig, const Aig_Obj_t* F_SAig);
void 			addVarToSolver(sat_solver* pSat, int varNum, int val);
int 			getCnfCoVarNum(Cnf_Dat_t* cnf, Aig_Man_t* aig, int nthCo);
lit 			addRlToSolver(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<int>& r);
lit 			addRlToSolver_rec(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<int>& r, int start, int end);
lit 			OR(sat_solver* pSat, lit lh, lit rh);
void 			addCnfToSolver(sat_solver* pSat, Cnf_Dat_t* cnf);
Cnf_Dat_t* 		buildErrorFormula(sat_solver* pSat, Aig_Man_t* SAig,
					vector<vector<int> > &r0, vector<vector<int> > &r1);
bool 			callSATfindCEX(Aig_Man_t* SAig,vector<int>& cex,
					vector<vector<int> > &r0, vector<vector<int> > &r1);
bool 			getNextCEX(Aig_Man_t*&SAig,vector<int>& cex, int& m,
					vector<vector<int> > &r0, vector<vector<int> > &r1);
bool 			populateStoredCEX(Aig_Man_t* SAig,
					vector<vector<int> > &r0, vector<vector<int> > &r1);
void 			evaluateAig(Aig_Man_t* formula, const vector<int> &cex);
Aig_Obj_t* 		satisfiesVec(Aig_Man_t* formula, const vector<int>& cex, const vector<int>& coObjs);
Aig_Obj_t* 		generalize(Aig_Man_t*pMan, vector<int> cex, const vector<int>& rl);
bool 			Aig_Support_rec(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId, map<Aig_Obj_t*,bool>& memo);
bool 			Aig_Support(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId);
Aig_Obj_t* 		Aig_AndAigs(Aig_Man_t* pMan, Aig_Obj_t* Aig1, Aig_Obj_t* Aig2);
void 			updateAbsRef(Aig_Man_t* pMan, vector<vector<int> > &r0, vector<vector<int> > &r1,
					const vector<int> &cex, const int &m);
Aig_Man_t* 		compressAig(Aig_Man_t* SAig);
Aig_Man_t* 		compressAigByNtk(Aig_Man_t* SAig);
void 			checkSupportSanity(Aig_Man_t*pMan, vector<vector<int> > &r0, vector<vector<int> > &r1);
Aig_Obj_t* 		OR_rec(Aig_Man_t* SAig, vector<int>& nodes, int start, int end);
Aig_Obj_t* 		newOR(Aig_Man_t* SAig, vector<int>& nodes);
bool 			verifyResult(Aig_Man_t* SAig, vector<vector<int> >& r0,
					vector<vector<int> >& r1, bool deleteCos);
void 			checkCexSanity(Aig_Man_t* pMan, vector<int>& cex, vector<vector<int> >& r0,
					vector<vector<int> >& r1);
Aig_Obj_t* 		Aig_SubstituteVec(Aig_Man_t* pMan, Aig_Obj_t* initAig, vector<int>& varIdVec,
					vector<Aig_Obj_t*>& funcVec);
void 			Aig_ComposeVec_rec( Aig_Man_t * p, Aig_Obj_t * pObj, vector<Aig_Obj_t *>& pFuncVec,
					vector<Aig_Obj_t* >& iVarObjVec );
Aig_Obj_t*	 	Aig_ComposeVec( Aig_Man_t * p, Aig_Obj_t * pRoot, vector<Aig_Obj_t *>& pFuncVec,
					vector<int>& iVarVec );
void 			Sat_SolverWriteDimacsAndIS( sat_solver * p, char * pFileName,
					lit* assumpBegin, lit* assumpEnd, int incrementVars, vector<int>&IS );
int 			unigen_call(string fname, int nSamples);
bool 			unigen_fetchModels(Aig_Man_t* SAig, vector<vector<int> > &r0, 
							vector<vector<int> > &r1, map<int, int>& varNum2ID);
vector<lit>		setAllNegX(Cnf_Dat_t* SCnf, Aig_Man_t* SAig, int val);
int 			findK2Max(Aig_Man_t* SAig, vector<int>&cex, vector<vector<int> >&r0, vector<vector<int> >&r1, int k1Max);
int 			findK2Max_rec(sat_solver* pSat, Cnf_Dat_t* SCnf, vector<int>&cex, int k_start, int k_end, lit assump[]);
bool 			checkIsFUnsat(sat_solver* pSat, Cnf_Dat_t* SCnf, vector<int>&cex, int k, lit assump[]);
int populateK1Vec(Aig_Man_t* SAig, vector<vector<int> >&r0, vector<vector<int> >&r1);
int populateK2Vec(Aig_Man_t* SAig, vector<vector<int> >&r0, vector<vector<int> >&r1, int k1Max);
