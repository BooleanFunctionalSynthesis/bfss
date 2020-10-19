#ifndef HELPER_H
#define HELPER_H

#include <iostream>
#include <vector>
#include <map>
#include <unordered_map>
#include <set>
#include <queue>
#include <list>
#include <algorithm>
#include <fstream>
#include <sstream>
#include <ctime>
#include <chrono>
#include <signal.h>
#include "cxxopts.hpp"

#ifndef NO_UNIGEN
#include "cusp.h"
#else
namespace CMSat{
	class CUSP {
	public:
		static bool unigenRunning;
		static int getSolutionMapSize(){return 0;}
	};
}
#endif

#define ABC_NAMESPACE NS_ABC

extern "C" {
#include "misc/util/abc_global.h"
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
#include "bdd/cudd/cuddInt.h"
#include "bdd/cudd/cudd.h"
}
namespace ABC_NAMESPACE {
	extern "C" {
	Aig_Man_t * Abc_NtkToDar(Abc_Ntk_t * pNtk, int fExors, int fRegisters);
	Abc_Ntk_t * Abc_NtkFromAigPhase(Aig_Man_t * pMan);
	}
}

using namespace std;
using namespace ABC_NAMESPACE;

#define STR_HELPER(X)		#X
#define STR(X)				STR_HELPER(X)
#define UNIGEN_OUT_DIR		"out"
#define UNIGEN_INPUT_FNAME 	"errorFormula"
#define UNIGEN_OUTPT_FNAME	"unigen_output.txt"
#define UNIGEN_DIMAC_FNAME 	UNIGEN_INPUT_FNAME ".cnf"
#define UNIGEN_MODEL_FNAME	UNIGEN_INPUT_FNAME "_0.txt"
#define UNIGEN_OUTPT_FPATH	UNIGEN_OUTPT_FNAME
#define UNIGEN_MODEL_FPATH	UNIGEN_OUT_DIR "/" UNIGEN_MODEL_FNAME
#define UNIGEN_DIMAC_FPATH 	UNIGEN_DIMAC_FNAME
#define UNIGEN_PY 			"UniGen2.py"
#define UNIGEN_SAMPLES_DEF	110000
#define UNIGEN_THREADS_DEF	19
#define INIT_COLLAPSE_PARAM	4
#define REF_COLLAPSE_PARAM	3
#define UNIGEN_THRESHOLD 	0.3
#define WAIT_SAMPLES_DEF 	110
#define FMCAD_SIZE_THRESH	1e6
#define UNATE_TIMEOUT		3600

// #define DEBUG
// #define DEBUG_CHUNK
// #define COMPARE_SAIGS // Uncomment to compare 2 SAigs
#ifdef DEBUG
	#define OUT( x ) cout << "DEBUG: " << x << endl
#else
	#define OUT( x )
#endif

typedef std::chrono::time_point<std::chrono::steady_clock> chrono_steady_time;
#define TIME_NOW			 std::chrono::steady_clock::now()
#define TIME_MEASURE_START   helper_time_measure_start = TIME_NOW;
#define TIME_MEASURE_ELAPSED (std::chrono::duration_cast<std::chrono::microseconds>(TIME_NOW-helper_time_measure_start).count()/1000000.0)
extern  chrono_steady_time helper_time_measure_start;
extern  chrono_steady_time main_time_start;

class  edge;
class  node;
class  Nnf_Man;

enum sType {skolemR0, skolemR1, skolemRx};
struct optionStruct {
	bool 	proactiveProp;
	bool 	useABCSolver;
	bool 	evalAigAtNode;
	string 	benchmark;
	string 	outFName;
	string 	varsOrder;
	sType 	skolemType;
	int 	numSamples;
	int 	numThreads;
	int 	c1;
	int 	c2;
	bool 	useFmcadPhase;
	bool	unigenBackground;
	double 	unigenThreshold;
	int 	waitSamples;
	bool 	monoSkolem;
	bool 	reverseOrder;
	bool 	noRevSub;
	bool 	verify;
	bool 	noUnate;
	bool 	noSyntacticUnate;
	bool 	noSemanticUnate;
	int 	fmcadSizeThreshold;
	int 	unateTimeout;
	bool 	checkSatOnly;
	bool 	checkWDNNF;
	bool 	useBDD;
};

extern vector<int> varsSInv;
extern vector<int> varsXF, varsXS;
extern vector<int> varsYF, varsYS; // to be eliminated
extern int numOrigInputs, numX, numY;
extern vector<string> varsNameX, varsNameY;
extern Abc_Frame_t* pAbc;
extern sat_solver* m_pSat;
extern Cnf_Dat_t* m_FCnf;
extern lit m_f;
extern vector<bool>  useR1AsSkolem;
extern int numFixes;
extern int numCEX;
extern int numCEXUsed;
extern cxxopts::Options optParser;
extern cxxopts::Options optParserOrdering;
extern optionStruct options;
extern optionStruct optionsOriginal;
extern vector<vector<int> > k2Trend;
extern double sat_solving_time;
extern double verify_sat_solving_time;
extern double reverse_sub_time;
extern vector<vector<int>> CiCloudIth;
extern vector<vector<int>> CoIth;
extern int F_SAigIndex;
extern int FPrime_SAigIndex;

int 			CommandExecute(Abc_Frame_t* pAbc, string cmd);
vector<string> 	tokenize( const string& p_pcstStr, char delim );
string 			type2String(Aig_Type_t t);
bool 			Equate(sat_solver *pSat, int varA, int varB);
bool 			Xor(sat_solver *pSat, int varA, int varB);
Abc_Ntk_t* 		getNtk(string pFileName, bool fraig);
int 			getNumY(string varsFile);
void 			populateVars(Abc_Ntk_t* FNtk, Nnf_Man& nnf, string varsFile,
					vector<int>& varsXF, vector<int>& varsXS,
					vector<int>& varsYF, vector<int>& varsYS,
					map<string,int>& name2IdF, map<int,string>& id2NameF);
Aig_Obj_t* 		Aig_SubstituteConst(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, int one);
Aig_Obj_t* 		Aig_Substitute(Aig_Man_t* pMan, Aig_Obj_t* initAig, int varId, Aig_Obj_t* func);
void			initializeCompose(Aig_Man_t* SAig, vector<Aig_Obj_t* >& Fs,
					vector<vector<int> >& r0, vector<vector<int> >& r1, vector<int>& unate);
void			initializeComposeCloudInputs(Aig_Man_t* SAig, vector<Aig_Obj_t* >& Fs,
					vector<vector<int> >& r0, vector<vector<int> >& r1, vector<int>& unate);
bool 			addVarToSolver(sat_solver* pSat, int varNum, int val);
int 			getCnfCoVarNum(Cnf_Dat_t* cnf, Aig_Man_t* aig, int nthCo);
lit 			addRlToSolver(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<int>& r);
lit 			addRlToSolver_rec(sat_solver* pSat, Cnf_Dat_t* GCnf, Aig_Man_t* GAig, const vector<int>& r, int start, int end);
lit 			OR(sat_solver* pSat, lit lh, lit rh);
bool 			addCnfToSolver(sat_solver* pSat, Cnf_Dat_t* cnf);
pair<Cnf_Dat_t*,bool> buildErrorFormula(sat_solver* pSat, Aig_Man_t* SAig,
					vector<vector<int> > &r0, vector<vector<int> > &r1);
bool 			callSATfindCEX(Aig_Man_t* SAig,vector<int>& cex,
					vector<vector<int> > &r0, vector<vector<int> > &r1);
bool 			getNextCEX(Aig_Man_t*&SAig, int& M, int& k1Level, int& k1MaxLevel, vector<vector<int> > &r0, vector<vector<int> > &r1);
bool 			populateCEX(Aig_Man_t* SAig,
					vector<vector<int> > &r0, vector<vector<int> > &r1);
bool 			populateStoredCEX(Aig_Man_t* SAig,
					vector<vector<int> > &r0, vector<vector<int> > &r1, bool fetch);
void 			evaluateAig(Aig_Man_t* formula, const vector<int> &cex);
Aig_Obj_t* 		satisfiesVec(Aig_Man_t* formula, const vector<int>& cex, const vector<int>& coObjs, bool reEvaluate);
Aig_Obj_t* 		generalize(Aig_Man_t*pMan, vector<int> cex, const vector<int>& rl);
bool 			Aig_Support_rec(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId, map<Aig_Obj_t*,bool>& memo);
bool 			Aig_Support(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId);
vector<Aig_Obj_t *> Aig_SupportVec(Aig_Man_t* pMan, Aig_Obj_t* root);
Aig_Obj_t* 		Aig_AndAigs(Aig_Man_t* pMan, Aig_Obj_t* Aig1, Aig_Obj_t* Aig2);
Aig_Obj_t* 		Aig_OrAigs(Aig_Man_t* pMan, Aig_Obj_t* Aig1, Aig_Obj_t* Aig2) ;
Aig_Obj_t* 		AND_rec(Aig_Man_t* SAig, vector<Aig_Obj_t* >& nodes, int start, int end);
Aig_Obj_t* 		newAND(Aig_Man_t* SAig, vector<Aig_Obj_t* >& nodes) ;
Aig_Obj_t* 		projectPi(Aig_Man_t* pMan, const vector<int> &cex, const int m);
void 			updateAbsRef(Aig_Man_t*&pMan, int M, int k1Level, int k1MaxLevel, vector<vector<int> > &r0, vector<vector<int> > &r1);
Aig_Man_t* 		compressAig(Aig_Man_t* SAig);
Aig_Man_t* 		compressAigByNtk(Aig_Man_t* SAig);
Aig_Man_t* 		compressAigByNtkMultiple(Aig_Man_t* SAig, int times);
void 			checkSupportSanity(Aig_Man_t*pMan, vector<vector<int> > &r0, vector<vector<int> > &r1);
Aig_Obj_t* 		OR_rec(Aig_Man_t* SAig, vector<int>& nodes, int start, int end);
Aig_Obj_t* 		newOR(Aig_Man_t* SAig, vector<int>& nodes);
void 			verifyResult(Aig_Man_t*&SAig, vector<vector<int> >& r0,
					vector<vector<int> >& r1, bool deleteCos);
void 			checkCexSanity(Aig_Man_t* pMan, vector<int>& cex, vector<vector<int> >& r0,
					vector<vector<int> >& r1);
Aig_Obj_t* 		Aig_SubstituteVec(Aig_Man_t* pMan, Aig_Obj_t* initAig, vector<int> varIdVec,
					vector<Aig_Obj_t*>& funcVec);
vector<Aig_Obj_t* >	Aig_SubstituteVecVec(Aig_Man_t* pMan, Aig_Obj_t* initAig, vector<vector<Aig_Obj_t*> >& funcVecs);
void 			Aig_ComposeVec_rec( Aig_Man_t * p, Aig_Obj_t * pObj, vector<Aig_Obj_t *>& pFuncVec,
					vector<Aig_Obj_t* >& iVarObjVec );
Aig_Obj_t*	 	Aig_ComposeVec( Aig_Man_t * p, Aig_Obj_t * pRoot, vector<Aig_Obj_t *>& pFuncVec,
					vector<int>& iVarVec );
void 			Aig_VecVecConeUnmark_rec(Aig_Obj_t * pObj);
void 			Aig_ComposeVecVec_rec(Aig_Man_t* p, Aig_Obj_t* pObj, vector<vector<Aig_Obj_t*> >& pFuncVecs);
vector<Aig_Obj_t* > Aig_ComposeVecVec(Aig_Man_t* p, Aig_Obj_t* pRoot, vector<vector<Aig_Obj_t*> >& pFuncVecs);
void 			Sat_SolverWriteDimacsAndIS( sat_solver * p, char * pFileName,
					lit* assumpBegin, lit* assumpEnd, vector<int>&IS, vector<int>&retSet);
int 			unigen_call(string fname, int nSamples, int nThreads);
bool 			unigen_fetchModels(Aig_Man_t* SAig, vector<vector<int> > &r0,
							vector<vector<int> > &r1, bool more);
vector<lit>		setAllNegX(Cnf_Dat_t* SCnf, Aig_Man_t* SAig, int val);
int 			findK2Max(Aig_Man_t* SAig, sat_solver* m_pSat, Cnf_Dat_t* m_FCnf, vector<int>&cex,
							vector<vector<int> >&r0, vector<vector<int> >&r1, int k1Max, int prevM);
int 			findK2Max_rec(sat_solver* pSat, Cnf_Dat_t* SCnf, vector<int>&cex, int k_start, int k_end, lit assump[]);
bool 			checkIsFUnsat(sat_solver* pSat, Cnf_Dat_t* SCnf, vector<int>&cex, int k, lit assump[]);
int 			filterAndPopulateK1Vec(Aig_Man_t* SAig, vector<vector<int> >&r0, vector<vector<int> >&r1, int prevM);
int 			filterAndPopulateK1VecFast(Aig_Man_t* SAig, vector<vector<int> >&r0, vector<vector<int> >&r1, int prevM);
int				populateK2Vec(Aig_Man_t* SAig, vector<vector<int> >&r0, vector<vector<int> >&r1, int prevM);
void 			initializeAddR1R0toR();
void			collapseInitialLevels(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1);
void			propagateR1Cofactors(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1);
void			propagateR0Cofactors(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1);
void			propagateR_Cofactors(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1);
void			propagateR0R1Cofactors(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1);
void			chooseSmallerR_(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1);
void			chooseR_(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1);
void			parseOptions(int argc, char * argv[]);
void			parseOptionsOrdering(int argc, char * argv[]);
void 			printK2Trend();
void 			monoSkolem(Aig_Man_t*&pMan, vector<vector<int> > &r0, vector<vector<int> > &r1);
string			getFileName(string s);
int 			checkUnateSyntacticAll(Aig_Man_t* FAig, vector<int>&unate);
int 			checkUnateSemanticAll(Aig_Man_t* FAig, vector<int>&unate);
int 			checkUnateSemAll(Aig_Man_t* FAig, vector<int>&unate);//Same as checkUnateSemanticAll but more memory efficient
void 			populateVars(Abc_Ntk_t* FNtk, string varsFile, vector<string>& varOrder,
					vector<int>& varsXF, vector<int>& varsYF,
					map<string,int>& name2IdF, map<int,string>& id2NameF);
void 			substituteUnates(Aig_Man_t* &pMan, vector<int>&unate);
void 			saveSkolems(Aig_Man_t* SAig, vector<int>& r_Aigs);
void 			printAig(Aig_Man_t* pMan);
int 			Aig_DagSizeWithConst(Aig_Obj_t * pObj);
void			printBDDNode(DdManager* ddMan, DdNode* obj);
void			printBDD(DdManager* ddMan, DdNode* f);

template<class T>
void print(T v) {
	cout << v;
}

template<class T>
void print(vector<T> v, string delim) {
	for (int i = 0; i < v.size(); ++i) {
		print(v[i]);
		cout << delim;
	}
}

#endif
