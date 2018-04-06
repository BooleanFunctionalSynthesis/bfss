#include "helper.h"
// #include "formula.h"
#include "nnf.h"

using namespace ABC_NAMESPACE;

vector<vector<int> > storedCEX;
vector<int> storedCEX_k1;
vector<int> storedCEX_k2;
vector<bool> storedCEX_unused;
vector<int> nodeIdtoN;
bool new_flag = true;
bool SwitchToABCSolver = false;
int numUnigenCalls = 0;
vector<bool> addR1R0toR0;
vector<bool> addR1R0toR1;
vector<bool> useR1AsSkolem;
unordered_map<string, int> cexSeen;
int numFixes = 0;
int numCEX   = 0;
int numCEXUsed = 0;
bool initCollapseDone = false;
cxxopts::Options optParser("bfss", "bfss: Blazingly Fast Skolem Synthesis");
optionStruct options;
optionStruct optionsOriginal;
vector<vector<int> > k2Trend;
vector<vector<bool> > storedCEX_r0Sat;
vector<vector<bool> > storedCEX_r1Sat;
int exhaustiveCollapsedTill = 0;
// int unigen_argc = 15;
// int unigen_samples_argnum = 1;
// int unigen_threads_argnum = 2;
// int unigen_cnfname_argnum = 13;
// char* unigen_argv[] = {"./unigen", "--samples=2200", "--threads=4", "--kappa=0.638", \
// 						"--pivotUniGen=27.0", "--maxTotalTime=72000", "--startIteration=0", \
// 						"--maxLoopTime=3000", "--tApproxMC=1", "--pivotAC=60", "--gaussuntil=400", \
// 						"--verbosity=0", "--multisample", UNIGEN_DIMAC_FNAME, UNIGEN_MODEL_FPATH};
int unigen_argc = 8;
int unigen_samples_argnum = 1;
int unigen_threads_argnum = 2;
int unigen_cnfname_argnum = 7;
char* unigen_argv[] = {"./scalmc", "--samples=2200", "--threads=4", "--kappa=0.638", \
						"--startIteration=0", \
						"--tApproxMC=1", "--pivotAC=60", \
						UNIGEN_DIMAC_FNAME};
pthread_t unigen_threadId = -1;
map<int, int> varNum2ID;
map<int, int> varNum2R0R1;
int solsJustFetched = 0;
vector<bool> collapsedInto;
int F_SAigIndex = -1;
int FPrime_SAigIndex = -1;

////////////////////////////////////////////////////////////////////////
///                      HELPER FUNCTIONS                            ///
////////////////////////////////////////////////////////////////////////
void parseOptions(int argc, char * argv[]) {
	bool lazy;
	string skolemType;
	optParser.positional_help("");
	optParser.add_options()
		("b, benchmark", "Specify the benchmark (required)", cxxopts::value<string>(options.benchmark), "FILE")
		("v, varsOrder", "Specify the variable ordering", cxxopts::value<string>(options.varsOrder), "FILE")
		("o, out", "Specify the output file (default: <benchmark>_result.v)", cxxopts::value<string>(options.outFName), "FILE")
		("skolem", "Specify skolem function to be used (r0/r1/rx)", cxxopts::value<string>(skolemType)->default_value("rx"))
		("a, ABC", "Use ABC's solver for SAT calls", cxxopts::value<bool>(options.useABCSolver))
		("e, evalAigAtNode", "Efficiently evaluate AIG on a need-only basis", cxxopts::value<bool>(options.evalAigAtNode))
		("l, lazy", "Don't propagate r0/r1 proactively", cxxopts::value<bool>(lazy))
		("h, help", "Print this help")
		("s, samples", "Number of unigen samples requested per call (default: " STR(UNIGEN_SAMPLES_DEF) ")", cxxopts::value<int>(options.numSamples), "N")
		("t, threads", "Number of unigen threads (default: " STR(UNIGEN_THREADS_DEF) ")", cxxopts::value<int>(options.numThreads), "N")
		("i, initCollapseParam", "Number of initial levels to collapse (default: " STR(INIT_COLLAPSE_PARAM) ")", cxxopts::value<int>(options.c1), "N")
		("r, refCollapseParam", "Number of levels to collapse k1 onwards (default: " STR(REF_COLLAPSE_PARAM) ")", cxxopts::value<int>(options.c2), "N")
		("f, fmcad", "Use FMCAD phase in update abstraction refinement", cxxopts::value<bool>(options.useFmcadPhase))
		("u, unigenBackground", "Run UniGen in background (faster)", cxxopts::value<bool>(options.unigenBackground))
		("unigenThreshold", "Threshold fraction of cex below which to switch error formula (default: " STR(UNIGEN_THRESHOLD) ")", cxxopts::value<double>(options.unigenThreshold), "N")
		("w, waitSamples", "Number of solutions to wait for when Unigen runs in parallel (default: " STR(WAIT_SAMPLES_DEF) ")", cxxopts::value<int>(options.waitSamples), "N")
		("m, monoSkolem", "Run MonoSkolem algorithm", cxxopts::value<bool>(options.monoSkolem))
		("reverseOrder", "Use reversed variable orderings", cxxopts::value<bool>(options.reverseOrder))
		("noRevSub", "Don't reverse substitute", cxxopts::value<bool>(options.noRevSub))
		("verify", "Veify computed skolem functions", cxxopts::value<bool>(options.verify))
		("noUnate", "Don't find and substitute unates", cxxopts::value<bool>(options.noUnate))
		("noSyntacticUnate", "Don't use Syntactic unateness checks", cxxopts::value<bool>(options.noSyntacticUnate))
		("noSemanticUnate", "Don't use Semantic unateness checks", cxxopts::value<bool>(options.noSemanticUnate))
		("fmcadSizeThresh", "Size after which to turn off fmcad (default: " STR(FMCAD_SIZE_THRESH) ")", cxxopts::value<int>(options.fmcadSizeThreshold), "N")
		("unateTimeout", "Timeout for unate checks (default: " STR(UNATE_TIMEOUT) ")", cxxopts::value<int>(options.unateTimeout), "N")
		("checkSatOnly", "Exit if SAT", cxxopts::value<bool>(options.checkSatOnly))
		("checkWDNNF", "check if wDNNF", cxxopts::value<bool>(options.checkWDNNF))
		("positional",
			"Positional arguments: these are the arguments that are entered "
			"without an option", cxxopts::value<std::vector<string>>())
		;

	optParser.parse_positional({"benchmark", "varsOrder","positional"});
	optParser.parse(argc, argv);

	if(options.varsOrder == "")
		options.varsOrder = options.benchmark.substr(0,options.benchmark.find_last_of('.')) + "_varstoelim.txt";

	SwitchToABCSolver = options.useABCSolver;
	options.proactiveProp = !lazy;

	if (optParser.count("help")) {
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (!optParser.count("benchmark")) {
		cerr << endl << "Error: Benchmark not specified" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (!optParser.count("samples")) {
		options.numSamples = UNIGEN_SAMPLES_DEF;
	}
	else if(options.useABCSolver) {
		cerr << endl << "Error: Sample count and ABC's solver are exclusive" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}
	else if(options.numSamples <= 0) {
		cerr << endl << "Error: Sample count must be positive" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (!optParser.count("waitSamples")) {
		options.waitSamples = WAIT_SAMPLES_DEF;
	}
	else if(options.useABCSolver) {
		cerr << endl << "Error: waitSamples and ABC's solver are exclusive" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}
	else if(options.numSamples < 0) {
		cerr << endl << "Error: waitSamples must be non-negative" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}
	else if(options.numSamples < 0) {
		cerr << endl << "Error: waitSamples must be non-negative" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (!optParser.count("threads")) {
		options.numThreads = UNIGEN_THREADS_DEF;
	}
	else if(options.useABCSolver) {
		cerr << endl << "Error: Number of threads and ABC's solver are exclusive" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}
	else if(options.numThreads <= 0) {
		cerr << endl << "Error: Number of threads must be positive" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (!optParser.count("initCollapseParam")) {
		options.c1 = INIT_COLLAPSE_PARAM;
	}
	else if(options.c1 < 0) {
		cerr << endl << "Error: Initial collapse levels must be non-negative" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (options.unigenBackground && options.useABCSolver) {
		cerr << endl << "Error: unigenBackground and ABC's solver are exclusive" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (options.verify && options.noRevSub) {
		cerr << endl << "Error: Cannot verify without reverse substitution" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (!optParser.count("refCollapseParam")) {
		options.c2 = REF_COLLAPSE_PARAM;
	}
	else if(options.c2 < 0) {
		cerr << endl << "Error: Refinement collapse levels (after k1) must be non-negative" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (!optParser.count("unigenThreshold")) {
		options.unigenThreshold = UNIGEN_THRESHOLD;
	}
	else if(options.useABCSolver) {
		cerr << endl << "Error: unigenThreshold and ABC's solver are exclusive" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}
	else if(!options.unigenBackground) {
		cerr << endl << "Error: unigenThreshold works only with unigenBackground (-u)" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}
	else if(options.unigenThreshold < 0) {
		cerr << endl << "Error: unigenThreshold must be non-negative" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if(skolemType == "r0")
		options.skolemType = sType::skolemR0;
	else if(skolemType == "r1")
		options.skolemType = sType::skolemR1;
	else if(skolemType == "rx")
		options.skolemType = sType::skolemRx;
	else {
		cerr << endl << "Error: " << skolemType << " is an invalid skolemType" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (!optParser.count("out")) {
		options.outFName = getFileName(options.benchmark) + "_result.v";
	}

	options.noUnate = options.noUnate || options.monoSkolem;

	if (!optParser.count("fmcadSizeThresh")) {
		options.fmcadSizeThreshold = FMCAD_SIZE_THRESH;
	}
	else if(options.fmcadSizeThreshold < 0) {
		cerr << endl << "Error: FMCAD Size threshold must be non-negative" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	if (!optParser.count("unateTimeout")) {
		options.unateTimeout = UNATE_TIMEOUT;
	}
	else if(options.unateTimeout < 0) {
		cerr << endl << "Error: Unate timeout must be non-negative" << endl << endl;
		cout << optParser.help({"", "Group"}) << std::endl;
		exit(0);
	}

	optionsOriginal = options;

	unigen_argv[1] = (char*)((new string("--samples="+to_string(options.numSamples)))->c_str());
	unigen_argv[2] = (char*)((new string("--threads="+to_string(options.numThreads)))->c_str());
	unigen_argv[13] = (char*)((new string(getFileName(options.benchmark) + "_" + UNIGEN_DIMAC_FPATH))->c_str());

	cout << "Configuration: " << endl;
	cout << "{" << endl;
	cout << "\t benchmark:            " << options.benchmark << endl;
	cout << "\t varsOrder:            " << options.varsOrder << endl;
	cout << "\t out:                  " << options.outFName << endl;
	cout << "\t skolemType:           " << options.skolemType << endl;
	cout << "\t useABCSolver:         " << options.useABCSolver << endl;
	cout << "\t evalAigAtNode:        " << options.evalAigAtNode << endl;
	cout << "\t proactiveProp:        " << options.proactiveProp << endl;
	cout << "\t numSamples:           " << options.numSamples << endl;
	cout << "\t numThreads:           " << options.numThreads << endl;
	cout << "\t initCollapseParam:    " << options.c1 << endl;
	cout << "\t refCollapseParam:     " << options.c2 << endl;
	cout << "\t useFmcadPhase:        " << options.useFmcadPhase << endl;
	cout << "\t unigenBackground:     " << options.unigenBackground << endl;
	cout << "\t unigenThreshold:      " << options.unigenThreshold << endl;
	cout << "\t waitSamples:          " << options.waitSamples << endl;
	cout << "\t monoSkolem:           " << options.monoSkolem << endl;
	cout << "\t reverseOrder:         " << options.reverseOrder << endl;
	cout << "\t noRevSub:             " << options.noRevSub << endl;
	cout << "\t verify:               " << options.verify << endl;
	cout << "\t noUnate:              " << options.noUnate << endl;
	cout << "\t fmcadSizeThreshold:   " << options.fmcadSizeThreshold << endl;
	cout << "\t unateTimeout:         " << options.unateTimeout << endl;
	cout << "\t checkSatOnly:         " << options.checkSatOnly << endl;
	cout << "}" << endl;
}

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

bool Equate(sat_solver *pSat, int varA, int varB) {
	lit Lits[3];
	assert(varA!=0 && varB!=0);
	bool retval = true;
	// A -> B
	Lits[0] = toLitCond( abs(-varA), -varA<0 );
	Lits[1] = toLitCond( abs(varB), varB<0 );
	if(!sat_solver_addclause( pSat, Lits, Lits + 2 )) {
		cerr << "Warning: In addCnfToSolver, sat_solver_addclause failed" << endl;
		retval = false;
	}

	// B -> A
	Lits[0] = toLitCond( abs(varA), varA<0 );
	Lits[1] = toLitCond( abs(-varB), -varB<0 );
	if(!sat_solver_addclause( pSat, Lits, Lits + 2 )) {
		cerr << "Warning: In addCnfToSolver, sat_solver_addclause failed" << endl;
		retval = false;
	}
	return retval;
}

bool Xor(sat_solver *pSat, int varA, int varB) {
	lit Lits[3];
	assert(varA!=0 && varB!=0);
	bool retval = true;

	// A or B
	Lits[0] = toLitCond( abs(varA), varA<0 );
	Lits[1] = toLitCond( abs(varB), varB<0 );
	if(!sat_solver_addclause( pSat, Lits, Lits + 2 )) {
		cerr << "Warning: In addCnfToSolver, sat_solver_addclause failed" << endl;
		retval = false;
	}

	// -A or -B
	Lits[0] = toLitCond( abs(-varA), -varA<0 );
	Lits[1] = toLitCond( abs(-varB), -varB<0 );
	if(!sat_solver_addclause( pSat, Lits, Lits + 2 )) {
		cerr << "Warning: In addCnfToSolver, sat_solver_addclause failed" << endl;
		retval = false;
	}
	return retval;
}

Abc_Ntk_t*  getNtk(string pFileName, bool fraig) {
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
	cmd = fraig?initCmd:"balance";
	if (CommandExecute(pAbc, cmd)) { // Simplify
		return NULL;
	}

	Abc_Ntk_t* pNtk =  Abc_FrameReadNtk(pAbc);
	// Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
	return pNtk;
}

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
void populateVars(Abc_Ntk_t* FNtk, Nnf_Man& nnf, string varsFile,
	vector<int>& varsXF, vector<int>& varsXS,
	vector<int>& varsYF, vector<int>& varsYS,
	map<string,int>& name2IdF, map<int,string>& id2NameF) {

	int i;
	Abc_Obj_t* pPi;
	string line;

	Abc_NtkForEachCi( FNtk, pPi, i ) {
		string variable_name = Abc_ObjName(pPi);
		name2IdF[variable_name] = pPi->Id;
	}
	#ifdef DEBUG_CHUNK
		OUT( "Prim Inputs F:" );
		Abc_NtkForEachCi( FNtk, pPi, i ) {
			OUT( i << ": " << pPi->Id << ", " << Abc_ObjName(pPi) );
		}
	#endif
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
	for(auto it : varsXF) {
		// cout << "nnf.getNewAigNodeID: " << it << "->" << nnf.getNewAigNodeID(it) << endl;
		// varsXS.push_back(nnf.getNewAigNodeID(it));
		varsXS.push_back(it);
		assert(varsXS.back() != -1);
	}
	for(auto it : varsYF) {
		// cout << "nnf.getNewAigNodeID: " << it << "->" << nnf.getNewAigNodeID(it) << endl;
		// varsYS.push_back(nnf.getNewAigNodeID(it));
		varsYS.push_back(it);
		assert(varsYS.back() != -1);
	}

	if(options.reverseOrder)
		reverse(varsYS.begin(),varsYS.end());

	numX = varsXS.size();
	numY = varsYS.size();

	if(numY <= 0) {
		cout << "Var File " + varsFile + " is empty!" << endl;
		cerr << "Var File " + varsFile + " is empty!" << endl;
		assert(numY > 0);
	}


	// for (int i = 0; i < numX; ++i) {
	// 	varsSInv[varsXS[i]] = i;
	// 	varsSInv[numOrigInputs + varsXS[i]] = numOrigInputs + i;
	// }
	// for (int i = 0; i < numY; ++i) {
	// 	varsSInv[varsYS[i]] = numX + i;
	// 	varsSInv[numOrigInputs + varsYS[i]] = numOrigInputs + numX + i;
	// }
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
	Aig_Obj_t* currFI = Aig_ObjIsCo(Aig_Regular(initAig))? initAig->pFanin0: initAig;
	Aig_Obj_t* afterCompose = Aig_Compose(pMan, currFI, constf, varId-1);
	assert(!Aig_ObjIsCo(Aig_Regular(afterCompose)));
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
	Aig_Obj_t* currFI = Aig_ObjIsCo(Aig_Regular(initAig))? initAig->pFanin0: initAig;
	func = Aig_ObjIsCo(Aig_Regular(func))? func->pFanin0: func;
	Aig_Obj_t* afterCompose = Aig_Compose(pMan, currFI, func, varId-1);
	assert(!Aig_ObjIsCo(Aig_Regular(afterCompose)));
	return afterCompose;
}

Aig_Obj_t* Aig_SubstituteVec(Aig_Man_t* pMan, Aig_Obj_t* initAig, vector<int> varIdVec,
	vector<Aig_Obj_t*>& funcVec) {
	Aig_Obj_t* currFI = Aig_ObjIsCo(Aig_Regular(initAig))? initAig->pFanin0: initAig;
	for (int i = 0; i < funcVec.size(); ++i) {
		funcVec[i] = Aig_ObjIsCo(Aig_Regular(funcVec[i]))? funcVec[i]->pFanin0: funcVec[i];
	}
	for (int i = 0; i < varIdVec.size(); ++i) {
		varIdVec[i]--;
	}
	Aig_Obj_t* afterCompose = Aig_ComposeVec(pMan, currFI, funcVec, varIdVec);
	assert(!Aig_ObjIsCo(Aig_Regular(afterCompose)));
	return afterCompose;
}

vector<Aig_Obj_t* > Aig_SubstituteVecVec(Aig_Man_t* pMan, Aig_Obj_t* initAig,
	vector<vector<Aig_Obj_t*> >& funcVecs) {
	Aig_Obj_t* currFI;
	currFI = Aig_ObjIsCo(Aig_Regular(initAig))? initAig->pFanin0: initAig;
	for(int i = 0; i < funcVecs.size(); i++) {
		for (int j = 0; j < funcVecs[i].size(); ++j) {
			funcVecs[i][j] = Aig_ObjIsCo(Aig_Regular(funcVecs[i][j]))? funcVecs[i][j]->pFanin0: funcVecs[i][j];
		}
	}
	vector<Aig_Obj_t* > afterCompose = Aig_ComposeVecVec(pMan, currFI, funcVecs);
	for (int i = 0; i < afterCompose.size(); ++i) {
		assert(!Aig_ObjIsCo(Aig_Regular(afterCompose[i])));
	}
	return afterCompose;
}


/** Function
 * Composes inputs of SAig with appropriate delta and gamma, makes the resulting
 * objects COs and stores them in r0 and r1.
 * @param SAig [in out]     Aig Manager
 * @param r0   [out]        Underapproximates the Cannot-be-0 sets
 * @param r1   [out]        Underapproximates the Cannot-be-1 sets
 */
void initializeCompose(Aig_Man_t* SAig, vector<Aig_Obj_t* >& Fs,
		vector<vector<int> >& r0, vector<vector<int> >& r1, vector<int>& unate) {
	nodeIdtoN.resize(2*numOrigInputs);
	for(int i = 0; i < numX; i++) {
		nodeIdtoN[varsXS[i] - 1] = i;
		nodeIdtoN[numOrigInputs + varsXS[i] - 1] = numOrigInputs + i;
	}
	for(int i = 0; i < numY; i++) {
		nodeIdtoN[varsYS[i] - 1] = numX + i;
		nodeIdtoN[numOrigInputs + varsYS[i] - 1] = numOrigInputs + numX + i;
	}

	vector<vector<Aig_Obj_t* > > funcVecVec;
	vector<Aig_Obj_t* > retVec;
	vector<Aig_Obj_t* > funcVec;

	funcVec.resize(0);
	for(int i = 0; i < numX; ++i) {
		funcVec.push_back(Aig_ManObj(SAig, varsXS[i]));
	}
	for(int i = 0; i < numY; ++i) {
		funcVec.push_back(Aig_ManObj(SAig, varsYS[i]));
	}
	for(int i = 0; i < numX; ++i) {
		funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsXS[i])));
	}
	for(int i = 0; i < numY; ++i) {
		funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsYS[i])));
	}
	funcVecVec.push_back(funcVec);

	funcVec.resize(0);
	for(int i = 0; i < numX; ++i) {
		funcVec.push_back(Aig_ManObj(SAig, varsXS[i]));
	}
	for(int i = 0; i < numY; ++i) {
		funcVec.push_back(Aig_ManObj(SAig, numOrigInputs + varsYS[i]));
	}
	for(int i = 0; i < numX; ++i) {
		funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsXS[i])));
	}
	for(int i = 0; i < numY; ++i) {
		funcVec.push_back(Aig_Not(Aig_ManObj(SAig, numOrigInputs + varsYS[i])));
	}
	funcVecVec.push_back(funcVec);

	for(int i = 0; i < numY; ++i) {
		funcVec.resize(0);
		for(int j = 0; j < numX; j++) {
			funcVec.push_back(Aig_ManObj(SAig, varsXS[j]));
		}
		for(int j = 0; j < numY; j++) {
			if(j < i) {
				funcVec.push_back(Aig_ManConst1(SAig));
			} else if(j == i) {
				funcVec.push_back(Aig_ManConst0(SAig));
			} else {
				funcVec.push_back(Aig_ManObj(SAig, varsYS[j]));
			}
		}
		for(int j = 0; j < numX; j++) {
			funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsXS[j])));
		}
		for(int j = 0; j < numY; j++) {
			if(j <= i) {
				funcVec.push_back(Aig_ManConst1(SAig));
			} else {
				funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsYS[j])));
			}
		}
		funcVecVec.push_back(funcVec);
	}

	for(int i = 0; i < numY; ++i) {
		funcVec.resize(0);
		for(int j = 0; j < numX; j++) {
			funcVec.push_back(Aig_ManObj(SAig, varsXS[j]));
		}
		for(int j = 0; j < numY; j++) {
			if(j <= i) {
				funcVec.push_back(Aig_ManConst1(SAig));
			} else {
				funcVec.push_back(Aig_ManObj(SAig, varsYS[j]));
			}
		}
		for(int j = 0; j < numX; j++) {
			funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsXS[j])));
		}
		for(int j = 0; j < numY; j++) {
			if(j < i) {
				funcVec.push_back(Aig_ManConst1(SAig));
			} else if(j == i) {
				funcVec.push_back(Aig_ManConst0(SAig));
			} else {
				funcVec.push_back(Aig_Not(Aig_ManObj(SAig, varsYS[j])));
			}
		}
		funcVecVec.push_back(funcVec);
	}

	retVec = Aig_SubstituteVecVec(SAig, Aig_ManCo(SAig, 0), funcVecVec);
	Fs[0] = Aig_ObjCreateCo(SAig, retVec[0]);
	Fs[1] = Aig_ObjCreateCo(SAig, retVec[1]);
	for(int i = 0; i < numY; i++) {
		switch(unate[i]) {
			case -1:
				Aig_ObjCreateCo(SAig, Aig_Not(retVec[2 + i]));
				break;
			case 0:
				Aig_ObjCreateCo(SAig, Aig_ManConst0(SAig));
				break;
			case 1:
				Aig_ObjCreateCo(SAig, Aig_ManConst1(SAig));
				break;
		}
		r0[i].push_back(Aig_ManCoNum(SAig) - 1);
	}
	for(int i = 0; i < numY; i++) {
		switch(unate[i]) {
			case -1:
				Aig_ObjCreateCo(SAig, Aig_Not(retVec[2 + numY + i]));
				break;
			case 0:
				Aig_ObjCreateCo(SAig, Aig_ManConst1(SAig));
				break;
			case 1:
				Aig_ObjCreateCo(SAig, Aig_ManConst0(SAig));
				break;
		}
		r1[i].push_back(Aig_ManCoNum(SAig) - 1);
	}
}

/** Function
 * Asserts varNum to have value val
 * @param pSat      [in out]     Sat Solver
 * @param varNum    [in]         Variable number
 * @param val       [in]         Value to be assigned
 */
bool addVarToSolver(sat_solver* pSat, int varNum, int val) {
	lit l = toLitCond(varNum, (int)(val==0)?1:0);
	if(!sat_solver_addclause(pSat, &l, &l+1)) {
	// if(!sat_solver_clause_new(pSat, &l, &l+1, 0)) {
		cerr << "Warning: In addVarToSolver, sat_solver_addclause returned false" << endl;
		return false;
	}
	return true;
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
 * @param pSat      [in]        Sat Solver
 * @param lh        [in]        lhs
 * @param rh        [in]        rhs
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
 * Returns a new sat solver variable denoting AND of lh and rh
 * @param pSat      [in]        Sat Solver
 * @param lh        [in]        lhs
 * @param rh        [in]        rhs
 */
lit AND(sat_solver* pSat, lit lh, lit rh) {
	int nv = sat_solver_newvar(pSat);

	lit Lits[4];
	assert(lh!=0 && rh!=0);
	// lh and rh -> nv
	Lits[0] = toLitCond( abs( nv),  nv<0 );
	Lits[1] = toLitCond( abs(-lh), -lh<0 );
	Lits[2] = toLitCond( abs(-rh), -rh<0 );
	if(!sat_solver_addclause( pSat, Lits, Lits + 3 ))
		assert(false);

	// nv -> lh
	Lits[0] = toLitCond( abs( lh),  lh<0 );
	Lits[1] = toLitCond( abs(-nv), -nv<0 );
	if(!sat_solver_addclause( pSat, Lits, Lits + 2 ))
		assert(false);

	// nv -> rh
	Lits[0] = toLitCond( abs( rh),  rh<0 );
	Lits[1] = toLitCond( abs(-nv), -nv<0 );
	if(!sat_solver_addclause( pSat, Lits, Lits + 2 ))
		assert(false);

	return nv;
}

/** Function
 * Adds CNF Formula to Solver
 * @param pSat      [in]        Sat Solver
 * @param cnf       [in]        Cnf Formula
 */
bool addCnfToSolver(sat_solver* pSat, Cnf_Dat_t* cnf) {
	bool retval = true;
	sat_solver_setnvars(pSat, sat_solver_nvars(pSat) + cnf->nVars);
	for (int i = 0; i < cnf->nClauses; i++)
		if (!sat_solver_addclause(pSat, cnf->pClauses[i], cnf->pClauses[i+1])) {
			cerr << "Warning: In addCnfToSolver, sat_solver_addclause failed" << endl;
			retval = false;
		}
	return retval;
}

/** Function
 * Builds the ErrorFormula (see below) and returns SCnf.
 * F(X,Y') and !F(X,Y) and \forall i (y_i == !r1[i])
 * @param pSat      [in]        Sat Solver
 * @param SAig      [in]        Aig to build the formula from
 */
pair<Cnf_Dat_t*,bool> buildErrorFormula(sat_solver* pSat, Aig_Man_t* SAig,
	vector<vector<int> > &r0, vector<vector<int> > &r1, vector<int> &r0Andr1Vars) {
	Abc_Obj_t* pAbcObj;
	int i;
	bool allOk = true;

	// Build CNF
	Cnf_Dat_t* SCnf = Cnf_Derive(SAig, Aig_ManCoNum(SAig));
	allOk = allOk && addCnfToSolver(pSat, SCnf);

	#ifdef DEBUG_CHUNK
		// Cnf_DataPrint(SCnf,1);

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
	allOk = allOk && addVarToSolver(pSat, SCnf->pVarNums[Aig_ManCo(SAig, F_SAigIndex)->Id], 0);
	allOk = allOk && addVarToSolver(pSat, SCnf->pVarNums[Aig_ManCo(SAig, FPrime_SAigIndex)->Id], 1);

	r0Andr1Vars.resize(numY);

	for (int i = 0; i < numY; ++i) {
		// Adding variables for r0[i] & r1[i]
		int r1i = addRlToSolver(pSat, SCnf, SAig, r1[i]);
		int r0i  = addRlToSolver(pSat, SCnf, SAig, r0[i]);
		int r0r1 = AND(pSat, r0i, r1i);
		r0Andr1Vars[i] = r0r1;

		if(useR1AsSkolem[i]) {
			// Assert y_i == -r1[i]
			OUT("equating  ID:     "<<varsYS[i]<<"="<<-Aig_ManCo(SAig,r1[i][0])->Id);
			OUT("          varNum: "<<SCnf->pVarNums[varsYS[i]]<<"="<<-r1i);
			allOk = allOk && Equate(pSat, SCnf->pVarNums[varsYS[i]], -r1i);
		}
		else {
			// Assert y_i == r0[i]
			OUT("equating  ID:     "<<varsYS[i]<<"="<<Aig_ManCo(SAig,r0[i][0])->Id);
			OUT("          varNum: "<<SCnf->pVarNums[varsYS[i]]<<"="<<r0i);
			allOk = allOk && Equate(pSat, SCnf->pVarNums[varsYS[i]], r0i);
		}
	}
	return make_pair(SCnf,allOk);
}

/** Function
 * Builds the ErrorFormula, Calls Sat Solver on it, populates cex.
 * Returns false if UNSAT.
 * @param pSat      [in]        Sat Solver
 * @param SAig      [in]        Aig to build the formula from
 * @param cex       [out]       Counter-example, contains values of X Y neg_X neg_Y in order.
 */
bool callSATfindCEX(Aig_Man_t* SAig,vector<int>& cex,
	vector<vector<int> > &r0, vector<vector<int> > &r1) {
	OUT("callSATfindCEX..." );
	bool return_val;

	// Milking to check if CEX is still valid
	if(true) {
		// cout << "milking"<<endl;
		for (int i = numY-1; i >= 0; --i)
		{
			assert(useR1AsSkolem[i]);
			evaluateAig(SAig,cex);
			bool r1i = false;
			for(auto r1El: r1[i]) {
				if(Aig_ManCo(SAig, r1El)->iData == 1) {
					r1i = true;
					break;
				}
			}
			cex[numX + i] = (int) !r1i;
		}
		evaluateAig(SAig,cex);

		if(Aig_ManCo(SAig, F_SAigIndex)->iData != 1) { //CEX still spurious, return
			// cout << "CEX still spurious, returning..." << endl;
			return true;
		}
	}
	// cout << "milked, not spurious"<<endl;

	vector<int> r0Andr1Vars(numY);

	sat_solver *pSat = sat_solver_new();
	auto cnf_flag  = buildErrorFormula(pSat, SAig, r0, r1, r0Andr1Vars);
	Cnf_Dat_t *SCnf  = cnf_flag.first;
	bool allOk = cnf_flag.second;

	OUT("Simplifying..." );
	if(!allOk or !sat_solver_simplify(pSat)) {
		OUT("Formula is trivially unsat");
		return_val = false;
	}
	else {
		OUT("Solving..." );
		vector<lit> assumptions = setAllNegX(SCnf, SAig, false);
		int status = sat_solver_solve(pSat,
						&assumptions[0], &assumptions[0] + numX,
						(ABC_INT64_T)0, (ABC_INT64_T)0,
						(ABC_INT64_T)0, (ABC_INT64_T)0);

		if (status == l_False) {
			OUT("Formula is unsat");
			return_val = false;
		}
		else if (status == l_True) {
			OUT("Formula is sat; get the CEX");

			cex.resize(2*numOrigInputs);
			for (int i = 0; i < numX; ++i) {
				cex[i] = SCnf->pVarNums[varsXS[i]];
			}
			for (int i = 0; i < numY; ++i) {
				cex[numX + i] = SCnf->pVarNums[varsYS[i]];
			}
			for (int i = 0; i < numX; ++i) {
				cex[numOrigInputs + i] = SCnf->pVarNums[varsXS[i] + numOrigInputs];
			}
			for (int i = 0; i < numY; ++i) {
				cex[numOrigInputs + numX + i] = SCnf->pVarNums[varsYS[i] + numOrigInputs];
			}

			int * v = Sat_SolverGetModel(pSat, &cex[0], cex.size());
			cex = vector<int>(v,v+cex.size());

			// Getting r0Andr1Vars is not useful here
			int * w = Sat_SolverGetModel(pSat, &r0Andr1Vars[0], r0Andr1Vars.size());
			r0Andr1Vars = vector<int>(w,w+r0Andr1Vars.size());

			#ifdef DEBUG_CHUNK
				OUT("Serial#  AigPID  Cnf-VarNum  CEX");
				OUT("__X__:");
				for (int i = 0; i < numX; ++i) {
					OUT(i<<":\t"<<varsXS[i]<<":\t"<<SCnf->pVarNums[Aig_ManObj(SAig, varsXS[i])->Id]<<":\t"<<cex[i]);
				}
				OUT("__Y__:");
				for (int i = 0; i < numY; ++i) {
					OUT(i<<":\t"<<varsYS[i]<<":\t"<<SCnf->pVarNums[Aig_ManObj(SAig, varsYS[i])->Id]<<":\t"<<cex[numX+i]);
					OUT("\t"<<Aig_ManCo(SAig, r1[i][0])->Id<<"\t"<<SCnf->pVarNums[Aig_ManCo(SAig, r1[i][0])->Id]<<"\t"<<sat_solver_var_value(pSat, SCnf->pVarNums[Aig_ManCo(SAig, r1[i][0])->Id]));
				}
				OUT("_!X__:");
				for (int i = 0; i < numX; ++i) {
					OUT(i<<":\t"<<varsXS[i]+numOrigInputs<<":\t"<<SCnf->pVarNums[Aig_ManObj(SAig, varsXS[i]+numOrigInputs)->Id]<<":\t"<<cex[i+numOrigInputs]);
				}
				OUT("_!Y__:");
				for (int i = 0; i < numY; ++i) {
					OUT(i<<":\t"<<varsYS[i]+numOrigInputs<<":\t"<<SCnf->pVarNums[Aig_ManObj(SAig, varsYS[i]+numOrigInputs)->Id]<<":\t"<<cex[numX+i+numOrigInputs]);
				}
			#endif

			return_val = true;
		}
	}
	sat_solver_delete(pSat);
	Cnf_DataFree(SCnf);
	return return_val;
}

/** Function
 * Returns next stored satisfying CEX. Calls Unigen if no CEX are stored.
 * Note: Uses only X-part of CEX
 * @param pSat      [in]        Sat Solver
 * @param SAig      [in]        Aig to build the formula from
 * @param cex       [out]       Counter-example, contains values of X Y neg_X neg_Y in order.
 * @param r0        [in]        Underapproximations of cant-be-0 sets.
 * @param r1        [in]        Underapproximations of cant-be-1 sets.
 */
bool getNextCEX(Aig_Man_t*&SAig, int& M, int& k1Level, int& k1MaxLevel, vector<vector<int> > &r0, vector<vector<int> > &r1) {
	OUT("getNextCEX...");

	while(true) {
		while(!storedCEX.empty()) {
			int k1Max = options.evalAigAtNode?
							filterAndPopulateK1VecFast(SAig, r0, r1, M) :
							filterAndPopulateK1Vec(SAig, r0, r1, M);
			if(storedCEX.empty())
				break;
			int k2Max = populateK2Vec(SAig, r0, r1, M);
			assert(storedCEX_k1.size() == storedCEX.size());
			assert(storedCEX_k2.size() == storedCEX.size());
			assert(storedCEX_unused.size() == storedCEX.size());
			// cout << "K1 K2 Data:" << endl;
			// for (int i = 0; i < storedCEX.size(); ++i) {
			// 	cout << i << ":\tk1: " << storedCEX_k1[i] << "\tk2: " << storedCEX_k2[i] << endl;
			// }
			cout << "k1Max: " << k1Max << "\tk2Max: " << k2Max << endl;
			M = k2Max;
			k1MaxLevel = k1Max;
			// vector<int> kFreq(numY, 0);
			// for(auto it: storedCEX_k1)
			// 	kFreq[it]++;
			// int maxFreqk1 = -1;
			// for(int i = 0; i < kFreq.size(); i++) {
			// 	if(maxFreqk1 < kFreq[i]) {
			// 		k1Level = i;
			// 		maxFreqk1 = kFreq[i];
			// 	}
			// }
			k1Level = 0;
			for (int i = 0; i < storedCEX_k2.size(); ++i)
				if (storedCEX_k2[i] == k2Max and k1Level < storedCEX_k1[i])
					k1Level = storedCEX_k1[i];

			return true;
		}

		// For functions that use prevM
		M = -1;

		// Ran out of CEX, fetch new
		if (populateCEX(SAig, r0, r1) == false)
			return false;
	}
}

bool populateCEX(Aig_Man_t* SAig,
	vector<vector<int> > &r0, vector<vector<int> > &r1) {
	if(!CMSat::CUSP::unigenRunning && CMSat::CUSP::getSolutionMapSize() == 0) {
		if(populateStoredCEX(SAig, r0, r1, true)) {
			// Add to numCEX
			numCEX += storedCEX.size();
			return true;
		}
		else {
			return false;
		}
	}
	cout << "Called more models " << endl;
	bool more = !(options.c1==0 and options.c2==0 and !options.useFmcadPhase and options.proactiveProp);
	unigen_fetchModels(SAig, r0, r1, more);
	int initSize = storedCEX.size();
	cout << "solsJustFetched: " << solsJustFetched << endl;
	cout << "initSize:        " << initSize << endl;
	int k1Max = options.evalAigAtNode?
					filterAndPopulateK1VecFast(SAig, r0, r1, -1) :
					filterAndPopulateK1Vec(SAig, r0, r1, -1);
	int finSize = storedCEX.size();
	cout << "finSize:         " << finSize << endl;
	if(solsJustFetched>0) {
		cout << "PACratio:           " << (((double)finSize)/solsJustFetched) << endl;
	}
	else {
		cout << "PACratio:           " << 0 << endl;
	}
	if(finSize < solsJustFetched*options.unigenThreshold and CMSat::CUSP::unigenRunning) {
		cout << "PACratio too low, Terminating Unigen prematurely" << endl;
		CMSat::CUSP::prematureKill = true;
		pthread_join(unigen_threadId, NULL);

		pthread_mutex_lock(&CMSat::mu_lock);
		CMSat::CUSP::unigenRunning = false;
		pthread_cond_signal(&CMSat::lilCondVar);
		pthread_mutex_unlock(&CMSat::mu_lock);
		unigen_threadId = -1;
	}

	// if(!CMSat::CUSP::unigenRunning && CMSat::CUSP::getSolutionMapSize() == 0) {
	// 	if(populateStoredCEX(SAig, r0, r1, false)) {
	// 		// Add to numCEX
	// 		numCEX += storedCEX.size();
	// 		return true;
	// 	}
	// 	else {
	// 		return false;
	// 	}
	// }
	numCEX += storedCEX.size();
	return true;
}

/** Function
 * Calls Unigen on the error formula, populates storedCEX
 * @param SAig      [in]        Aig to build the formula from
 * @param r0        [in]        Underapproximations of cant-be-0 sets.
 * @param r1        [in]        Underapproximations of cant-be-1 sets.
 */
bool populateStoredCEX(Aig_Man_t* SAig,
	vector<vector<int> > &r0, vector<vector<int> > &r1, bool fetch) {
	OUT("populating Stored CEX...");
	bool return_val;
	int status;
	vector<int> r0Andr1Vars(numY);

	sat_solver *pSat = sat_solver_new();
	auto cnf_flag  = buildErrorFormula(pSat, SAig, r0, r1, r0Andr1Vars);
	Cnf_Dat_t *SCnf  = cnf_flag.first;
	bool allOk = cnf_flag.second;

	OUT("Simplifying..." );
	if(!allOk or !sat_solver_simplify(pSat)) { // Found Skolem Functions
		OUT("Formula is trivially unsat");
		sat_solver_delete(pSat);
		Cnf_DataFree(SCnf);
		return false;
	}

	if( ! SwitchToABCSolver) {
		// Compute IS
		vector<int> IS;
		for(int i=0; i<numX; ++i) // X
			IS.push_back(SCnf->pVarNums[varsXS[i]]);

		// Compute ReturnSet
		vector<int> RS;
		for(int i=0; i<numX; ++i) // X
			RS.push_back(SCnf->pVarNums[varsXS[i]]);
		for(int i=0; i<numY; ++i) // Y
			RS.push_back(SCnf->pVarNums[varsYS[i]]);
		for(int i=0; i<numY; ++i) // r0Andr1Vars
			RS.push_back(r0Andr1Vars[i]);
		assert(r0Andr1Vars.size()==numY);

		string fname = getFileName(options.benchmark) + "_" + UNIGEN_DIMAC_FPATH + "_" + to_string(numUnigenCalls);
		// Print Dimacs
		vector<lit> assumptions = setAllNegX(SCnf, SAig, false);
		Sat_SolverWriteDimacsAndIS(pSat, (char*)fname.c_str(),
			&assumptions[0], &assumptions[0] + numX, IS, RS);

		Aig_ManPrintStats(SAig);
		// Call Unigen
		status = unigen_call(fname, options.numSamples, options.numThreads);
	}
	else {
		status = -1; // Switch to ABC
	}

	if(status == 0) { // UNSAT
		OUT("Formula is UNSAT");
		return_val = false;
	}
	else if(status == 1) { // Successful
		// Read CEX
		varNum2ID.clear();
		for(int i=0; i<numX; ++i)
			varNum2ID[SCnf->pVarNums[varsXS[i]]] = i;
		for(int i=0; i<numY; ++i)
			varNum2ID[SCnf->pVarNums[varsYS[i]]] = numX + i;
		for(int i=0; i<numX; ++i)
			varNum2ID[SCnf->pVarNums[numOrigInputs + varsXS[i]]] = numOrigInputs + i;
		for(int i=0; i<numY; ++i)
			varNum2ID[SCnf->pVarNums[numOrigInputs + varsYS[i]]] = numOrigInputs + numX + i;

		// For fetching r0[m] and r1[m] from solver
		varNum2R0R1.clear();
		for(int i=0; i<r0Andr1Vars.size(); i++) {
			varNum2R0R1[r0Andr1Vars[i]] = i;
		}

		if(fetch) {
			if(unigen_fetchModels(SAig, r0, r1, 0)) {
				OUT("Formula is SAT, stored CEXs");
				return_val = true;
			}
			else {
				OUT("Formula is UNSAT");
				return_val = false;
			}
		}
		else
			return_val = true;
	}
	else { // Too little solutions
		assert(status == -1);
		OUT("UNIGEN says too little solutions");
		if(!SwitchToABCSolver)
			cout << "\nSwitching to ABC's solver" << endl;

		SwitchToABCSolver = true;

		vector<lit> assumptions = setAllNegX(SCnf, SAig, false);

		auto start = std::chrono::steady_clock::now();
		status = sat_solver_solve(pSat,
						&assumptions[0], &assumptions[0] + numX,
						(ABC_INT64_T)0, (ABC_INT64_T)0,
						(ABC_INT64_T)0, (ABC_INT64_T)0);
		auto end = std::chrono::steady_clock::now();
		sat_solving_time += std::chrono::duration_cast<std::chrono::microseconds>(end - start).count()/1000000.0;

		if (status == l_False) {
			OUT("Formula is unsat");
			return_val = false;
		}
		else if (status == l_True) {
			OUT("Formula is sat; storing CEX");

			vector<int> cex(2*numOrigInputs);
			for (int i = 0; i < numX; ++i) {
				cex[i] = SCnf->pVarNums[varsXS[i]];
			}
			for (int i = 0; i < numY; ++i) {
				cex[numX + i] = SCnf->pVarNums[varsYS[i]];
			}
			for (int i = 0; i < numX; ++i) {
				cex[numOrigInputs + i] = SCnf->pVarNums[varsXS[i] + numOrigInputs];
			}
			for (int i = 0; i < numY; ++i) {
				cex[numOrigInputs + numX + i] = SCnf->pVarNums[varsYS[i] + numOrigInputs];
			}
			int * v = Sat_SolverGetModel(pSat, &cex[0], cex.size());
			cex = vector<int>(v,v+cex.size());

			// Obtaining value of k1
			int * w = Sat_SolverGetModel(pSat, &r0Andr1Vars[0], r0Andr1Vars.size());
			r0Andr1Vars = vector<int>(w,w+r0Andr1Vars.size());
			int k1 = numY-1;
			while(r0Andr1Vars[k1] == 0) {k1--;}
			assert(k1>=0);

			storedCEX.push_back(cex);
			storedCEX_k1.push_back(k1);
			storedCEX_k2.push_back(-1);
			storedCEX_unused.push_back(true);
			storedCEX_r0Sat.push_back(vector<bool>(numY, false));
			storedCEX_r1Sat.push_back(vector<bool>(numY, false));
			return_val = true;
		}
	}

	sat_solver_delete(pSat);
	Cnf_DataFree(SCnf);
	return return_val;
}

/** Function
 * This evaluates all nodes of the Aig using values from cex
 * The value of the node is stored in pObj->iData
 * @param formula   [in]        Aig Manager
 * @param cex       [in]        counter-example
 */
void evaluateAig(Aig_Man_t* formula, const vector<int> &cex) {
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
	Aig_ManObj(formula,0)->iData = 1;

	Aig_ManForEachObj(formula, pObj, i) {
		if(pObj->Id > 2*numOrigInputs) {
			pObj->iData = 1;
			int ld, rd;
			if(Aig_ObjFanin0(pObj) != NULL) {
				ld = Aig_ObjFanin0(pObj)->iData;
				if(Aig_IsComplement(pObj->pFanin0))
					ld = 1 - ld;

				pObj->iData *= ld;
			}
			if(Aig_ObjFanin1(pObj) != NULL) {
				rd = Aig_ObjFanin1(pObj)->iData;
				if(Aig_IsComplement(pObj->pFanin1))
					rd = 1 - rd;

				pObj->iData *= rd;
			}
		}
	}
	return;
}

/** Function
 * This evaluates all leaves of the Aig using values from cex
 * The value of the node is stored in pObj->iData
 * @param formula   [in]        Aig Manager
 * @param cex       [in]        counter-example
 */
void evaluateXYLeaves(Aig_Man_t* formula, const vector<int> &cex) {
	for (int i = 0; i < numX; ++i) {
		Aig_ManObj(formula, varsXS[i])->iData = cex[i];
		Aig_ObjSetTravIdCurrent(formula, Aig_ManObj(formula, varsXS[i]));
	}
	for (int i = 0; i < numY; ++i) {
		Aig_ManObj(formula, varsYS[i])->iData = cex[numX + i];
		Aig_ObjSetTravIdCurrent(formula, Aig_ManObj(formula, varsYS[i]));
	}

	// Setting Const1
	Aig_ManObj(formula,0)->iData = 1;
	Aig_ObjSetTravIdCurrent(formula, Aig_ManObj(formula,0));
}

/** Function
 * This evaluates and returns head using values from leaves
 * The value of the leaves is stored in pObj->iData
 * @param formula   [in]        Aig Manager
 * @param head      [in]        node to be evaluated
 */
bool evaluateAigAtNode(Aig_Man_t* formula, Aig_Obj_t*head) {

	int isComplement = Aig_IsComplement(head);
	head = Aig_Regular(head);

	if(Aig_ObjIsTravIdCurrent(formula, head)) {
		assert(head->iData == 0 or head->iData == 1);
		return (bool) isComplement xor head->iData;
	}

	if(Aig_ObjIsCo(head)) {
		Aig_ObjSetTravIdCurrent(formula,head);
		head->iData = (int) evaluateAigAtNode(formula, Aig_ObjChild0(head));
		return (bool) isComplement xor head->iData;
	}

	bool lc, rc;
	lc = evaluateAigAtNode(formula, Aig_ObjChild0(head));
	if(lc)
		rc = evaluateAigAtNode(formula, Aig_ObjChild1(head));
	else
		rc = true;

	head->iData = (int) (lc and rc);
	Aig_ObjSetTravIdCurrent(formula,head);
		return (bool) isComplement xor head->iData;
}

/** Function
 * Finds an element in coObjs that satisfies cex.
 * Returns the object, if found. Else, returns NULL.
 * Call evaluateAig(...) before this function.
 * @param formula   [in]        Aig Manager
 * @param cex       [in]        Counterexample
 * @param coObjs    [in]        Co numbers in Aig Manager to check
 */
Aig_Obj_t* satisfiesVec(Aig_Man_t* formula, const vector<int>& cex, const vector<int>& coObjs, bool reEvaluate) {

	if(reEvaluate)
		evaluateAig(formula, cex);

	OUT("satisfiesVec...");

	Aig_Obj_t* currRet = NULL;
	int currMinSupp = std::numeric_limits<int>::max();

	for(int i = 0; i < coObjs.size(); i++) {
		OUT("Accessing Co "<<coObjs[i]<<" Id "<< Aig_ManCo(formula,coObjs[i])->Id);

		if(Aig_ManCo(formula,coObjs[i])->iData == 1) {
			OUT("Satisfied ID " << Aig_ManCo(formula,coObjs[i])->Id);

			vector<Aig_Obj_t* > tempSupp = Aig_SupportVec(formula, Aig_ManCo(formula,coObjs[i]));
			int tempSuppLen = tempSupp.size();

			if(tempSuppLen < currMinSupp) {
				currMinSupp = tempSuppLen;
				currRet = Aig_ManCo(formula,coObjs[i]);
			}
		}
	}
	OUT("Nothing satisfied");
	return currRet;
}

/** Function
 * Performs the function of the GENERALIZE routine as mentioned in FMCAD paper.
 * @param pMan      [in]        Aig Manager
 * @param cex       [in]        counter-example to be generalized
 * @param rl        [in]        Underaproximations of Cant-be sets
 */
Aig_Obj_t* generalize(Aig_Man_t*pMan, vector<int> cex, const vector<int>& rl) {
	return satisfiesVec(pMan, cex, rl, true);
}

/** Function
 * Recursively checks if inpNodeId lies in support of root.
 * @param pMan      [in]        Aig Manager
 * @param root      [in]        Function to check support of
 * @param inpNodeId [in]        ID of input variable to be checked
 * @param memo      [in]        A map for memoization
 */
bool Aig_Support_rec(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId, map<Aig_Obj_t*,bool>& memo) {
	if(root == NULL)
		return false;

	if(root->Id == inpNodeId)
		return true;

	if(Aig_ObjIsCi(root) || Aig_ObjIsConst1(root))
		return false;

	if(memo.find(root) != memo.end())
		return memo[root];

	bool result = false;
	if(Aig_ObjFanin0(root) != NULL)
		result = result || Aig_Support_rec(pMan, Aig_ObjFanin0(root), inpNodeId, memo);
	if(Aig_ObjFanin1(root) != NULL)
		result = result || Aig_Support_rec(pMan, Aig_ObjFanin1(root), inpNodeId, memo);

	memo[root] = result;
	return result;
}

/** Function
 * Checks if inpNodeId lies in support of root.
 * @param pMan      [in]        Aig Manager
 * @param root      [in]        Function to check support of
 * @param inpNodeId [in]        ID of input variable to be checked
 */
bool Aig_Support(Aig_Man_t* pMan, Aig_Obj_t* root, int inpNodeId) {
	map<Aig_Obj_t*,bool> memo;
	return Aig_Support_rec(pMan,Aig_Regular(root),inpNodeId,memo);
}

void Aig_ConeSupportVecAndMark_rec(Aig_Obj_t * pObj, set<Aig_Obj_t *>&retSupport) {
    assert(!Aig_IsComplement(pObj));
    if(pObj == NULL || Aig_ObjIsMarkA(pObj)) {
    	return;
    }
    else if(Aig_ObjIsConst1(pObj)) {
    	Aig_ObjSetMarkA(pObj);
    	return;
    }
    else if(Aig_ObjIsCi(pObj)) {
    	Aig_ObjSetMarkA(pObj);
		retSupport.insert(pObj);
		return;
    }

    Aig_ConeSupportVecAndMark_rec(Aig_ObjFanin0(pObj), retSupport);
    Aig_ConeSupportVecAndMark_rec(Aig_ObjFanin1(pObj), retSupport);

    assert(!Aig_ObjIsMarkA(pObj)); // loop detection
    Aig_ObjSetMarkA(pObj);
    return;
}

void Aig_ConeSupportVecUnmark_rec(Aig_Obj_t * pObj) {
    assert(!Aig_IsComplement(pObj));
    if(pObj == NULL || !Aig_ObjIsMarkA(pObj)) {
    	return;
    }
    else if(Aig_ObjIsConst1(pObj) || Aig_ObjIsCi(pObj)) {
    	Aig_ObjClearMarkA(pObj);
		return;
    }
    Aig_ConeSupportVecUnmark_rec(Aig_ObjFanin0(pObj));
    Aig_ConeSupportVecUnmark_rec(Aig_ObjFanin1(pObj));
    assert(Aig_ObjIsMarkA(pObj)); // loop detection
    Aig_ObjClearMarkA(pObj);
}

vector<Aig_Obj_t *> Aig_SupportVec(Aig_Man_t* pMan, Aig_Obj_t* root) {
    set<Aig_Obj_t *> retSupport;
    Aig_ConeSupportVecUnmark_rec(Aig_Regular(root));
    Aig_ConeSupportVecAndMark_rec(Aig_Regular(root), retSupport);
    Aig_ConeSupportVecUnmark_rec(Aig_Regular(root));
	return vector<Aig_Obj_t *>(retSupport.begin(), retSupport.end());
}

/** Function
 * Returns And of Aig1 and Aig2
 * @param pMan      [in]        Aig Manager
 * @param Aig1      [in]
 * @param Aig2      [in]
 */
Aig_Obj_t* Aig_AndAigs(Aig_Man_t* pMan, Aig_Obj_t* Aig1, Aig_Obj_t* Aig2) {
	Aig_Obj_t* lhs = Aig_ObjIsCo(Aig_Regular(Aig1))? Aig_Regular(Aig1)->pFanin0: Aig1;
	Aig_Obj_t* rhs = Aig_ObjIsCo(Aig_Regular(Aig2))? Aig_Regular(Aig2)->pFanin0: Aig2;
	return Aig_And(pMan, lhs, rhs);
}

/** Function
 * Returns Or of Aig1 and Aig2
 * @param pMan      [in]        Aig Manager
 * @param Aig1      [in]
 * @param Aig2      [in]
 */
Aig_Obj_t* Aig_OrAigs(Aig_Man_t* pMan, Aig_Obj_t* Aig1, Aig_Obj_t* Aig2) {
	Aig_Obj_t* lhs = Aig_ObjIsCo(Aig_Regular(Aig1))? Aig_Regular(Aig1)->pFanin0: Aig1;
	Aig_Obj_t* rhs = Aig_ObjIsCo(Aig_Regular(Aig2))? Aig_Regular(Aig2)->pFanin0: Aig2;
	return Aig_Or(pMan, lhs, rhs);
}

Aig_Obj_t* AND_rec(Aig_Man_t* SAig, vector<Aig_Obj_t* >& nodes, int start, int end) {
	// cout << "And_rec on start: " << start << " " << "end " << end << endl;
	assert(end > start);
	if(end == start+1)
		return nodes[start];

	int mid = (start+end)/2;
	Aig_Obj_t* lh = AND_rec(SAig, nodes, start, mid);
	Aig_Obj_t* rh = AND_rec(SAig, nodes, mid, end);
	Aig_Obj_t* nv = Aig_And(SAig, lh, rh);

	return nv;
}

Aig_Obj_t* newAND(Aig_Man_t* SAig, vector<Aig_Obj_t* >& nodes) {
	return AND_rec(SAig, nodes, 0, nodes.size());
}


Aig_Obj_t* projectPi(Aig_Man_t* pMan, const vector<int> &cex, const int m) {
	vector<Aig_Obj_t*> pi_m(numOrigInputs - m - 1);
	for(int i = 0; i < numX; i++) {
		pi_m[i] = (cex[i] == 1)?Aig_ManObj(pMan, varsXS[i]):Aig_Not(Aig_ManObj(pMan, varsXS[i]));
	}
	for(int i = m + 1; i < numY; i++) {
		pi_m[numX + i - m - 1] = (cex[numX + i] == 1)?Aig_ManObj(pMan, varsYS[i]):Aig_Not(Aig_ManObj(pMan, varsYS[i]));
	}
	return newAND(pMan, pi_m);
}

Aig_Obj_t* projectPiSmall(Aig_Man_t* pMan, const vector<int> &cex) {
	vector<Aig_Obj_t*> pi_m(numX);
	for(int i = 0; i < numX; i++) {
		pi_m[i] = (cex[i] == 1)?Aig_ManObj(pMan, varsXS[i]):Aig_Not(Aig_ManObj(pMan, varsXS[i]));
	}
	return newAND(pMan, pi_m);
}

/** Function
 * This updates r0 and r1 while eliminating cex
 * @param pMan      [in]        Aig Manager
 * @param r0        [in out]    Underaproximations of Cant-be-0 sets
 * @param r1        [in out]    Underaproximations of Cant-be-1 sets
 * @param cex       [in]        counter-example
 */
void updateAbsRef(Aig_Man_t*&pMan, int M, int k1Level, int k1MaxLevel, vector<vector<int> > &r0, vector<vector<int> > &r1) {
	OUT("updateAbsRef...");
	int k, l;
	Aig_Obj_t *mu0, *mu1, *mu, *pi1_m, *pi0_m, *pAigObj, *mu0_temp, *mu1_temp;
	mu0 = mu1 = mu = pi1_m = pi0_m = pAigObj = mu0_temp = mu1_temp = NULL;

	// cout << "addR1R0toR0: ";
	// for(auto it:addR1R0toR0)
	// 	cout << it << " ";
	// cout << endl;
	// cout << "addR1R0toR1: ";
	// for(auto it:addR1R0toR1)
	// 	cout << it << " ";
	// cout << endl;

	// have a global init collapse level
	int refCollapseStart, refCollapseEnd, fmcadPhaseStart, fmcadPhaseEnd;
	// does it suffice for just the cofactors for refCollapse
	assert(k1Level <= M);
	assert(k1Level >= exhaustiveCollapsedTill);

	// Calculate refCollapse Levels
	refCollapseStart = k1Level;
	while(collapsedInto[refCollapseStart] and refCollapseStart<=M) {refCollapseStart++;}
	refCollapseEnd = min(M, min(numY - 1, refCollapseStart + options.c2));
	if(refCollapseStart>M or collapsedInto[refCollapseStart])
		refCollapseEnd = refCollapseStart = k1Level;

	fmcadPhaseStart = (refCollapseEnd == refCollapseStart)?k1Level:refCollapseEnd;
	fmcadPhaseEnd = M;


	// ####################################
	//  SECTION A: 0 -> c1 ################
	// ####################################
	if(!initCollapseDone and options.c1>0) {

		int minK2 = numY;
		for(auto it:storedCEX_k2)
			if(it<minK2)
				minK2 = it;

		if(options.c1 >= minK2) {
			cout << "One time initial collapsing since c1=" << options.c1 << " >= minK2=" << minK2 << endl;
			for(int i = 0; i<options.c1; i++) {

				cout << "#1exhaustiveCollapsedTill = " << i+1 << endl;
				exhaustiveCollapsedTill = i+1;
				collapsedInto[i] = true;
				collapsedInto[i+1] = true;

				if(!addR1R0toR1[i] and !addR1R0toR0[i])
					continue;

				mu0 = newOR(pMan, r0[i]);
				mu1 = newOR(pMan, r1[i]);
				mu = Aig_AndAigs(pMan, mu0, mu1);


				// kill other Cos and have only this in r1[i + 1]
				if(addR1R0toR1[i]) {
					mu1 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 1);

					// Aig_ObjCreateCo(pMan, mu1);
					// r1[i+1].push_back(Aig_ManCoNum(pMan) - 1);
					for(auto it:r1[i+1]) {
						pAigObj = Aig_ManCo(pMan,it);
						Aig_ObjPatchFanin0(pMan, pAigObj, mu1);
					}

					addR1R0toR1[i] = false;
					addR1R0toR0[i+1] = true;
					addR1R0toR1[i+1] = true;
				}

				if(addR1R0toR0[i]) {
					mu0 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 0);
					// Aig_ObjCreateCo(pMan, mu0);
					// r0[i+1].push_back(Aig_ManCoNum(pMan) - 1);
					for(auto it:r0[i+1]) {
						pAigObj = Aig_ManCo(pMan,it);
						Aig_ObjPatchFanin0(pMan, pAigObj, mu0);
					}
					addR1R0toR0[i] = false;
					addR1R0toR0[i+1] = true;
					addR1R0toR1[i+1] = true;
				}

				int removed = Aig_ManCleanup(pMan);
				cout << "Removed " << removed <<" nodes" << endl;
			}
			cout << "compressAigByNtk" << endl;
			Aig_ManPrintStats(pMan);
			pMan = compressAigByNtk(pMan);
			Aig_ManPrintStats(pMan);
			initCollapseDone = true;
			// reset stored k1/k2 for cex known to have been fixed
			for (int i = 0; i < storedCEX.size(); ++i) {
				if(storedCEX_k1[i] < exhaustiveCollapsedTill) {
					storedCEX_k1[i] = -1;
				}
				if(storedCEX_k2[i] < exhaustiveCollapsedTill) {
					storedCEX_k2[i] = -1;
				}
			}
			return;
		}
	}

	list<int> releventCEX;
	for (int i = 0; i < storedCEX.size(); ++i) {
		if(storedCEX_k2[i] == M and storedCEX_k1[i] == k1Level)
			releventCEX.push_back(i);
	}


	// ########################################
	//  SECTION B: k1 -> k1+c2 ################
	// ########################################
	if(refCollapseStart <= exhaustiveCollapsedTill) {
		refCollapseStart = exhaustiveCollapsedTill;
	}
	if(refCollapseStart < refCollapseEnd)
		cout << "refcollapse " << refCollapseStart <<" to " << refCollapseEnd << endl;
	bool flag = false;
	for(int i = refCollapseStart; i<refCollapseEnd; i++) {

		if(exhaustiveCollapsedTill == i) {
			cout << "#2exhaustiveCollapsedTill = " << i+1 << endl;
			exhaustiveCollapsedTill = i+1;
			flag = true;
		}
		collapsedInto[i] = true;
		collapsedInto[i+1] = true;

		if(!addR1R0toR1[i] and !addR1R0toR0[i])
			continue;

		mu0 = newOR(pMan, r0[i]);
		mu1 = newOR(pMan, r1[i]);
		mu = Aig_AndAigs(pMan, mu0, mu1);

		if(addR1R0toR1[i]) {
			mu1 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 1);

			if(exhaustiveCollapsedTill == i+1) {
				for(auto it:r1[i+1]) {
					pAigObj = Aig_ManCo(pMan,it);
					Aig_ObjPatchFanin0(pMan, pAigObj, mu1);
				}
			}
			else {
				Aig_ObjCreateCo(pMan, mu1);
				r1[i+1].push_back(Aig_ManCoNum(pMan) - 1);
			}
			addR1R0toR1[i] = false;
			addR1R0toR0[i+1] = true;
			addR1R0toR1[i+1] = true;
		}

		if(addR1R0toR0[i]) {
			mu0 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 0);

			if(exhaustiveCollapsedTill == i+1) {
				for(auto it:r0[i+1]) {
					pAigObj = Aig_ManCo(pMan,it);
					Aig_ObjPatchFanin0(pMan, pAigObj, mu0);
				}
			}
			else {
				Aig_ObjCreateCo(pMan, mu0);
				r0[i+1].push_back(Aig_ManCoNum(pMan) - 1);
			}

			addR1R0toR0[i] = false;
			addR1R0toR0[i+1] = true;
			addR1R0toR1[i+1] = true;
		}

		// for(auto it = releventCEX.begin(); it != releventCEX.end();) {
		// 	if(!storedCEX_r0Sat[*it][i+1] && !storedCEX_r1Sat[*it][i+1])
		// 		releventCEX.erase(it++);
		// 	else
		// 		it++;
		// }

		if(flag) {
			int removed = Aig_ManCleanup(pMan);
			cout << "Removed " << removed <<" nodes" << endl;
		}
	}
	if(refCollapseStart <refCollapseEnd) {
		for (int i = 0; i < storedCEX.size(); ++i) {
			if(storedCEX_k1[i] < refCollapseEnd and
				storedCEX_k1[i] >= refCollapseStart) {
				storedCEX_k1[i] = -1;
			}
			if(storedCEX_k2[i] < refCollapseEnd and
				storedCEX_k2[i] >= refCollapseStart) {
				storedCEX_k2[i] = -1;
			}
		}
	}


	// #########################################
	// SECTION C: k1+c -> fmcad ################
	// #########################################
	if(optionsOriginal.useFmcadPhase) {
		int size = Aig_ManAndNum(pMan);
		if(size  > options.fmcadSizeThreshold and options.useFmcadPhase) {
			printf("Aig Size (%d) exceeded Threshold (%d), turning off fmcad\n",
					size, options.fmcadSizeThreshold);
			options.useFmcadPhase = false;
		}
		else if(size  <= options.fmcadSizeThreshold and !options.useFmcadPhase) {
			printf("Aig Size (%d) less than Threshold (%d), turning on fmcad\n",
					size, options.fmcadSizeThreshold);
			options.useFmcadPhase = true;
		}
	}
	if(options.useFmcadPhase and !releventCEX.empty()) {
		bool continueFmcad = true;
		fmcadPhaseStart = max(fmcadPhaseStart, exhaustiveCollapsedTill);
		cout << "fmcad from  " << fmcadPhaseStart << endl;

		mu0 = mu1 = NULL;
		int cexIndex = -1;
		int corrK2 = -1;
		int k = fmcadPhaseStart;
		for(int i = 0; i< storedCEX.size(); i++) {
			if(storedCEX_k1[i] == k and storedCEX_k2[i] == M) {
				if(corrK2 < storedCEX_k2[i]) {
					corrK2 = storedCEX_k2[i];
					cexIndex = i;
				}
			}
		}
		if(cexIndex == -1) {
			for(auto i:releventCEX) {
				if(((mu0_temp = generalize(pMan, storedCEX[i], r0[k])) !=NULL) and
				   ((mu1_temp = generalize(pMan, storedCEX[i], r1[k])) !=NULL))

					if(corrK2 < storedCEX_k2[i]) {
						corrK2 = storedCEX_k2[i];
						cexIndex = i;
						mu0 = mu0_temp;
						mu1 = mu1_temp;
					}
			}
		}
		else {
			mu0 = generalize(pMan, storedCEX[cexIndex], r0[k]);
			mu1 = generalize(pMan, storedCEX[cexIndex], r1[k]);
		}

		if(cexIndex != -1) {
			assert(mu0 and mu1);
			auto &cex = storedCEX[cexIndex];
			mu = Aig_AndAigs(pMan, mu0, mu1);
			int l = k+1;
			while(true) {
				assert(l<numY);
				if(Aig_Support(pMan, mu, varsYS[l])) {
					if(cex[numX + l] == 1) {
						mu1 = Aig_SubstituteConst(pMan, mu, varsYS[l], 1);
						Aig_ObjCreateCo(pMan, mu1);
						r1[l].push_back(Aig_ManCoNum(pMan)-1);
						if(storedCEX_r0Sat[cexIndex][l]) {
							mu0 = generalize(pMan,cex,r0[l]);
							mu = Aig_AndAigs(pMan, mu0, mu1);
						}
						else if(!storedCEX_r1Sat[cexIndex][l]) {
							cout << "fmcad break " << l << endl;
							break;
						}
					}
					else {
						mu0 = Aig_SubstituteConst(pMan, mu, varsYS[l], 0);
						Aig_ObjCreateCo(pMan, mu0);
						r0[l].push_back(Aig_ManCoNum(pMan)-1);
						if(storedCEX_r1Sat[cexIndex][l]) {
							mu1 = generalize(pMan,cex,r1[l]);
							mu = Aig_AndAigs(pMan, mu0, mu1);
						}
						else if(!storedCEX_r0Sat[cexIndex][l]) {
							cout << "fmcad break " << l << endl;
							break;
						}
					}
				}
				l = l+1;
			}
		}
		else {
			cout << "No cex available" << endl;
		}
	}


	// #################################
	// SECTION D: k2Fix ################
	// #################################
	k = M;
	l = M + 1;
	assert(k >= 0);
	assert(l < numY);

	if(exhaustiveCollapsedTill <= M) {
		bool fixR0 = false;
		bool fixR1 = false;
		for(int i = 0; i < storedCEX.size(); i++) {
			if(storedCEX_k2[i] == M) {
				if(storedCEX[i][numX + l] == 1) {
					if(!fixR1)
						pi1_m = projectPi(pMan, storedCEX[i], M);
					else
						pi1_m = Aig_OrAigs(pMan, pi1_m, projectPiSmall(pMan, storedCEX[i]));
					fixR1 = true;
					numFixes++;
					// cout << "Adding " << i << " to pi1_m" << endl;
				}
				else {
					if(!fixR0)
						pi0_m = projectPi(pMan, storedCEX[i], M);
					else
						pi0_m = Aig_OrAigs(pMan, pi0_m, projectPiSmall(pMan, storedCEX[i]));
					fixR0 = true;
					numFixes++;
					// cout << "Adding " << i << " to pi0_m" << endl;
				}
				if(storedCEX_unused[i]) {
					numCEXUsed++;
					storedCEX_unused[i] = false;
				}
			}
		}

		// bool addR1R0toR0_m = addR1R0toR0[M] and !options.proactiveProp and !options.useFmcadPhase;
		// bool addR1R0toR1_m = addR1R0toR1[M] and !options.proactiveProp and !options.useFmcadPhase;
		bool addR1R0toR0_m = false;
		bool addR1R0toR1_m = false;

		if((fixR0 and addR1R0toR0_m) or (fixR1 and addR1R0toR1_m)) {
			mu0 = newOR(pMan, r0[M]);
			mu1 = newOR(pMan, r1[M]);
			mu = Aig_AndAigs(pMan, mu0, mu1);
		}

		if(fixR0) {
			if(addR1R0toR0_m) {
				mu0 = Aig_OrAigs(pMan, mu, pi0_m);
				addR1R0toR0[M]   = false;
				addR1R0toR0[M+1] = true;
				addR1R0toR1[M+1] = true;
			}
			else {
				mu0 = pi0_m;
			}
			mu0 = Aig_SubstituteConst(pMan, mu0, varsYS[l], 0);
			Aig_ObjCreateCo(pMan, mu0);
			r0[l].push_back(Aig_ManCoNum(pMan) - 1);
		}

		if(fixR1) {
			if(addR1R0toR1_m) {
				mu1 = Aig_OrAigs(pMan, mu, pi1_m);
				addR1R0toR1[M]   = false;
				addR1R0toR0[M+1] = true;
				addR1R0toR1[M+1] = true;
			}
			else {
				mu1 = pi1_m;
			}
			mu1 = Aig_SubstituteConst(pMan, mu1, varsYS[l], 1);
			Aig_ObjCreateCo(pMan, mu1);
			r1[l].push_back(Aig_ManCoNum(pMan) - 1);
		}

		if(exhaustiveCollapsedTill==M and !addR1R0toR0[M] and !addR1R0toR1[M]) {
			cout << "#4exhaustiveCollapsedTill = " << M+1 << endl;
			exhaustiveCollapsedTill = M+1;
		}
	}
	else {
		cout << "Skipping k2Fix" << endl;
	}

	return;
}

/** Function
 * Compresses Aig using the compressAig() routine
 * Deletes SAig and returns a compressed version
 * @param SAig      [in]        Aig to be compressed
 */
Aig_Man_t* compressAig(Aig_Man_t* SAig) {
	OUT("Cleaning up...");
	int removed = Aig_ManCleanup(SAig);
	cout << "Removed " << removed <<" nodes" << endl;

	Aig_Man_t* temp = SAig;
	// Dar_ManCompress2( Aig_Man_t * pAig, int fBalance,
	//                  int fUpdateLevel, int fFanout,
	//                  int fPower, int fVerbose )
	OUT("Running Dar_ManCompress2...");
	SAig =  Dar_ManCompress2(SAig, 1, 1, 26, 1, 0);
	OUT("Stopping Old Aig Manager...");
	Aig_ManStop( temp );
	return SAig;
}

/** Function
 * Compresses Aig by converting it to an Ntk and performing a bunch of steps on it.
 * Deletes SAig and returns a compressed version
 * @param SAig      [in]        Aig to be compressed
 */
Aig_Man_t* compressAigByNtk(Aig_Man_t* SAig) {
	Aig_Man_t* temp;
	string command;

	OUT("Cleaning up...");
	int removed = Aig_ManCleanup(SAig);
	cout << "Removed " << removed <<" nodes" << endl;

	SAig =  Dar_ManCompress2(temp = SAig, 1, 1, 26, 1, 0);
	Aig_ManStop(temp);

	Abc_Ntk_t * SNtk = Abc_NtkFromAigPhase(SAig);
	Abc_FrameSetCurrentNetwork(pAbc, SNtk);

	// TODO: FIX
	if(options.evalAigAtNode) {
		command = "balance; rewrite -l; rewrite -lz; balance; rewrite -lz; \
					balance; rewrite -l; refactor -l; balance; rewrite -l; \
					rewrite -lz; balance; refactor -lz; rewrite -lz; balance;";
	} else {
		command = "fraig; balance; rewrite -l; rewrite -lz; balance; rewrite -lz; \
					balance; rewrite -l; refactor -l; balance; rewrite -l; \
					rewrite -lz; balance; refactor -lz; rewrite -lz; balance;";
	}

	if (Cmd_CommandExecute(pAbc, (char*)command.c_str())) {
		cout << "Cannot preprocess SNtk" << endl;
		return NULL;
	}
	SNtk = Abc_FrameReadNtk(pAbc);
	temp = Abc_NtkToDar(SNtk, 0, 0);
	Aig_ManStop(SAig);
	return temp;
}


/** Function
 * Compresses Aig by converting it to an Ntk and performing a bunch of steps on it.
 * Deletes SAig and returns a compressed version
 * @param SAig      [in]        Aig to be compressed
 * @param times     [in]        Number of compression cycles to be run
 */
Aig_Man_t* compressAigByNtkMultiple(Aig_Man_t* SAig, int times) {
	Aig_Man_t* temp;
	string command;

	OUT("Cleaning up...");
	int removed = Aig_ManCleanup(SAig);
	cout << "Removed " << removed <<" nodes" << endl;

	// SAig =  Dar_ManCompress2(temp = SAig, 1, 1, 26, 1, 0);
	// Aig_ManStop(temp);

	Abc_Ntk_t * SNtk = Abc_NtkFromAigPhase(SAig);
	Abc_FrameSetCurrentNetwork(pAbc, SNtk);

	// TODO: FIX
	assert(options.evalAigAtNode);
	command = "rewrite -lz; refactor -l;";

	cout << "balancing..." << endl;
	if (Cmd_CommandExecute(pAbc, "balance;")) {
		cout << "Cannot preprocess SNtk" << endl;
		return NULL;
	}

	for (int i = 0; i < times; ++i)	{
		cout << "cycle " << i << ": " << command;
		TIME_MEASURE_START
		if (Cmd_CommandExecute(pAbc, (char*)command.c_str())) {
			cout << "Cannot preprocess SNtk, took " << TIME_MEASURE_ELAPSED << endl;
			return NULL;
		}
		cout << "took " << TIME_MEASURE_ELAPSED << endl;
	}

	cout << "balancing..." << endl;
	if (Cmd_CommandExecute(pAbc, "balance;")) {
		cout << "Cannot preprocess SNtk" << endl;
		return NULL;
	}

	SNtk = Abc_FrameReadNtk(pAbc);
	temp = Abc_NtkToDar(SNtk, 0, 0);
	Aig_ManStop(SAig);
	return temp;
}

/** Function
 * Checks and asserts expected support invariants for r0 r1 F_SAig and FPrime_Saig
 * @param SAig      [in]        Aig to be compressed
 * @param r0        [in]
 * @param r1        [in]
 */
void checkSupportSanity(Aig_Man_t*pMan, vector<vector<int> > &r0, vector<vector<int> > &r1) {
	for (int i = 0; i < numY; ++i) {
		for(auto co_num:r0[i])
			for (int j = 0; j <= i; ++j)
				assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsYS[j]) == false);
		for(auto co_num:r1[i])
			for (int j = 0; j <= i; ++j)
				assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsYS[j]) == false);
	}
	for (int i = 0; i < numY; ++i) {
		for(auto r:r0)
			for(auto co_num:r)
				assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsYS[i] + numOrigInputs) == false);
		for(auto r:r1)
			for(auto co_num:r)
				assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsYS[i] + numOrigInputs) == false);
	}
	for (int i = 0; i < numX; ++i) {
		for(auto r:r0)
			for(auto co_num:r)
				assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsXS[i] + numOrigInputs) == false);
		for(auto r:r1)
			for(auto co_num:r)
				assert(Aig_Support(pMan, Aig_ManCo(pMan, co_num), varsXS[i] + numOrigInputs) == false);
	}

	Aig_Obj_t* F_SAig = Aig_ManCo(pMan,F_SAigIndex);
	Aig_Obj_t* FPrime_SAig = Aig_ManCo(pMan,FPrime_SAigIndex);

	for (int i = 0; i < numY; ++i) {
		assert(Aig_Support(pMan, F_SAig, varsYS[i] + numOrigInputs) == false);
		assert(Aig_Support(pMan, FPrime_SAig, varsYS[i]) == false);
	}
	for (int i = 0; i < numX; ++i) {
		assert(Aig_Support(pMan, F_SAig, varsXS[i] + numOrigInputs) == false);
		assert(Aig_Support(pMan, FPrime_SAig, varsXS[i] + numOrigInputs) == false);
	}
}

Aig_Obj_t* OR_rec(Aig_Man_t* SAig, vector<int>& nodes, int start, int end) {

	assert(end > start);

	if(end == start+1)
		return Aig_ObjChild0(Aig_ManCo(SAig,nodes[start]));

	int mid = (start+end)/2;
	Aig_Obj_t* lh = OR_rec(SAig, nodes, start, mid);
	Aig_Obj_t* rh = OR_rec(SAig, nodes, mid, end);
	Aig_Obj_t* nv = Aig_Or(SAig, lh, rh);

	return nv;
}

Aig_Obj_t* newOR(Aig_Man_t* SAig, vector<int>& nodes) {
	return OR_rec(SAig, nodes, 0, nodes.size());
}

void Aig_ObjDeleteCo( Aig_Man_t * p, Aig_Obj_t * pObj) {
	// Function Not Tested, use at your own risk!
	assert( Aig_ObjIsCo(pObj) );
	Aig_ObjDisconnect(p,pObj);
	pObj->pFanin0 = NULL;
	p->nObjs[pObj->Type]--;
	Vec_PtrWriteEntry( p->vObjs, pObj->Id, NULL );
	Aig_ManRecycleMemory( p, pObj );
	Vec_PtrRemove(p->vCos, pObj);
}

Aig_Obj_t* Aig_XOR(Aig_Man_t*p, Aig_Obj_t*p0, Aig_Obj_t*p1) {
	return Aig_Or( p, Aig_And(p, p0, Aig_Not(p1)), Aig_And(p, Aig_Not(p0), p1) );
}

bool verifyResult(Aig_Man_t*&SAig, vector<vector<int> >& r0,
	vector<vector<int> >& r1, bool deleteCos) {
	int i; Aig_Obj_t*pAigObj; int numAND;
	vector<int> skolemAig(numY);

	if(options.noRevSub) {
		cout << "noRevSub, exiting" << endl;
		return true;
	}

	OUT("Taking Ors..." << i);
	for(int i = 0; i < numY; i++) {
		if(useR1AsSkolem[i])
			pAigObj	= Aig_Not(newOR(SAig, r1[i]));
		else
			pAigObj	= newOR(SAig, r0[i]);
		pAigObj = Aig_ObjCreateCo(SAig,pAigObj);
		skolemAig[i] = Aig_ManCoNum(SAig)-1;
		assert(pAigObj!=NULL);
	}

	// Calculating Total un-substituted Size
	int max_before = 0;
	double avg_before = 0;
	for(auto it : skolemAig) {
		pAigObj = Aig_ObjChild0(Aig_ManCo(SAig, it));
		numAND = Aig_DagSizeWithConst(pAigObj);
		avg_before += numAND;
		if(max_before < numAND)
			max_before = numAND;
	}
	avg_before = avg_before*1.0/skolemAig.size();
	cout << "Final un-substituted num outputs: " << skolemAig.size() << endl;
	cout << "Final un-substituted AVG Size:    " << avg_before << endl;
	cout << "Final un-substituted MAX Size:    " << max_before << endl;


	if(deleteCos) {
		assert(false); // rescinded
		// Delete extra stuff
		set<int> requiredCOs;
		set<Aig_Obj_t*> redundantCos;
		for(auto it:skolemAig)
			requiredCOs.insert(Aig_ManCo(SAig,it)->Id);
		requiredCOs.insert(Aig_ManCo(SAig,F_SAigIndex)->Id);
		Aig_ManForEachCo( SAig, pAigObj, i) {
			if(requiredCOs.find(pAigObj->Id)==requiredCOs.end()) {
				redundantCos.insert(pAigObj);
			}
		}
		for(auto it:redundantCos) {
			Aig_ObjDeleteCo(SAig,it);
		}

		// Recompute skolemAig
		vector<pair<int, int> > vv(numY);
		i = 0;
		for(auto it:skolemAig)
			vv[i++] = make_pair(it,i);

		sort(vv.begin(), vv.end());
		i=1;
		for(auto it:vv) {
			skolemAig[it.second] = i++;
		}
	}

	// OUT("compressAigByNtk...");
	// SAig = compressAigByNtk(SAig);

	#ifdef DEBUG_CHUNK // Print SAig, r1, skolemAig
		cout << "\nSAig: " << endl;
		Aig_ManForEachObj( SAig, pAigObj, i )
			Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
		i=0;
		for(auto it:r1) {
			cout<<"r1["<<i<<"] : ";
			for(auto it2:it)
				cout<<it2<<" ";
			cout<<endl;
			i++;
		}
		i=0;
		for(auto it:skolemAig) {
			cout<<"skolemAig["<<i<<"] : " << skolemAig[i] << endl;
			i++;
		}
	#endif

	int i_temp;
	// Aig_ManForEachObj(SAig,pAigObj,i_temp) {
	// 	assert(Aig_ObjIsConst1(pAigObj) || Aig_ObjIsCi(pAigObj) || Aig_ObjIsCo(pAigObj) || (Aig_ObjFanin0(pAigObj) && Aig_ObjFanin1(pAigObj)));
	// }

	auto start = std::chrono::steady_clock::now();
	cout << "Reverse Substitution..." << endl;
	int iter = 0;
	for(int i = numY-2; i >= 0; --i) {
		iter++;
		Aig_Obj_t * curr = Aig_ManCo(SAig, skolemAig[i]);
		for(int j = i + 1; j < numY; ++j) {
			// Aig_ManForEachObj(SAig,pAigObj,i_temp) {
			// 	assert(Aig_ObjIsConst1(pAigObj) || Aig_ObjIsCi(pAigObj) || Aig_ObjIsCo(pAigObj) || (Aig_ObjFanin0(pAigObj) && Aig_ObjFanin1(pAigObj)));
			// }

			Aig_Obj_t* skolem_j = Aig_ObjChild0(Aig_ManCo(SAig,skolemAig[j]));
			curr = Aig_Substitute(SAig, curr, varsYS[j], skolem_j);
			assert(skolemAig[i]!=NULL);
			assert(Aig_ObjIsCo(Aig_Regular(curr))==false);
		}
		Aig_ObjPatchFanin0(SAig, Aig_ManCo(SAig, skolemAig[i]), curr);
		if(iter%30 == 0) {
			Aig_ManPrintStats( SAig );
			cout << "Compressing SAig..." << endl;
			SAig = compressAigByNtkMultiple(SAig, 2);
			assert(SAig != NULL);
			Aig_ManPrintStats( SAig );
		}
	}
	// SAig = compressAigByNtk(SAig);
	// Calculating Total reverse-substituted Size
	int max_after = 0;
	double avg_after = 0;
	for(auto it : skolemAig) {
		pAigObj = Aig_ObjChild0(Aig_ManCo(SAig, it));
		numAND = Aig_DagSizeWithConst(pAigObj);
		avg_after += numAND;
		if(max_after < numAND)
			max_after = numAND;
	}
	avg_after = avg_after*1.0/skolemAig.size();
	cout << "Final reverse-substituted num outputs: " << skolemAig.size() << endl;
	cout << "Final reverse-substituted AVG Size:    " << avg_after << endl;
	cout << "Final reverse-substituted MAX Size:    " << max_after << endl;
	Aig_ManPrintStats(SAig);

	auto end = std::chrono::steady_clock::now();
	reverse_sub_time = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count()/1000000.0;
	cout<< "Reverse substitute time: " << reverse_sub_time << endl;

	// save skolems to file
	saveSkolems(SAig, skolemAig);

	// For experimental purposes
	if(!options.verify)
		return true;
	else
		cout << "Verifying Result..." << endl;

	OUT("Final F Resubstitution...");
	Aig_Obj_t* F = Aig_ManCo(SAig, F_SAigIndex);
	for(int i = 0; i < numY; i++) {
		Aig_Obj_t* skolem_i = Aig_ObjChild0(Aig_ManCo(SAig,skolemAig[i]));
		F = Aig_Substitute(SAig, F, varsYS[i], skolem_i);
	}

	OUT("F Id:     "<<Aig_Regular(F)->Id);
	OUT("F compl:  "<<Aig_IsComplement(F));
	OUT("Aig_ObjChild0(Aig_ManCo(SAig, F_SAigIndex)) Id:     "<<Aig_Regular(Aig_ObjChild0(Aig_ManCo(SAig, F_SAigIndex)))->Id);
	OUT("Aig_ObjChild0(Aig_ManCo(SAig, F_SAigIndex)) compl:  "<<Aig_IsComplement(Aig_ObjChild0(Aig_ManCo(SAig, F_SAigIndex))));
	OUT("Aig_ObjChild0(Aig_ManCo(SAig, F_SAigIndex)):        "<<Aig_ObjChild0(Aig_ManCo(SAig, F_SAigIndex)));


	// F = Aig_Exor(SAig, F, Aig_ObjChild0(Aig_ManCo(SAig, 1)));
	// F = Aig_XOR(SAig, F, Aig_ObjChild0(Aig_ManCo(SAig, 1)));
	OUT("Aig_ManCoNum(SAig): "<<Aig_ManCoNum(SAig));

	F = Aig_ObjCreateCo(SAig, F);
	OUT("Aig_ManCoNum(SAig): "<<Aig_ManCoNum(SAig));
	int F_num = Aig_ManCoNum(SAig)-1;

	#ifdef DEBUG_CHUNK // Print SAig
		cout << "\nSAig: " << endl;
		Aig_ManForEachObj( SAig, pAigObj, i )
			Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
	#endif

	OUT("compressAigByNtk...");
	SAig = compressAigByNtk(SAig);

	sat_solver* pSat = sat_solver_new();
	Cnf_Dat_t* FCnf = Cnf_Derive(SAig, Aig_ManCoNum(SAig));
	addCnfToSolver(pSat, FCnf);

	lit LA[3];
	LA[0] = toLitCond(getCnfCoVarNum(FCnf, SAig, F_num),1);
	LA[1] = toLitCond(getCnfCoVarNum(FCnf, SAig, F_SAigIndex),0);

	bool return_val;
	start = std::chrono::steady_clock::now();
	int status = sat_solver_solve(pSat, LA, LA+2, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
	end = std::chrono::steady_clock::now();
	verify_sat_solving_time = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count()/1000000.0;

	if (status == l_False) {
		cout << "Verified!" << endl;
		return_val = true;
	}
	else if (status == l_True) {
		cout << "Not Verified!" << endl;
		return_val = false;
	}
	sat_solver_delete(pSat);
	Cnf_DataFree(FCnf);
	return return_val;
}

void checkCexSanity(Aig_Man_t* pMan, vector<int>& cex, vector<vector<int> >& r0,
	vector<vector<int> >& r1) {
	OUT("checkCexSanity...");
	evaluateAig(pMan,cex);

	int i;
	Aig_Obj_t* pAigObj;
	#ifdef DEBUG_CHUNK // Print SAig
		cout << "\nSAig: " << endl;
		Aig_ManForEachObj( pMan, pAigObj, i )
			Aig_ObjPrintVerbose( pAigObj, 1 ), cout<<"\t"<<pAigObj->iData, printf( "\n" );
	#endif

	for (int i = 0; i < numY; ++i)
	{
		OUT("\t checking for i=" << i);
		if(useR1AsSkolem[i])
			assert((cex[numX + i]==1) ^ (satisfiesVec(pMan, cex, r1[i], true)!=NULL));
		else
			assert(!((cex[numX + i]==1) ^ (satisfiesVec(pMan, cex, r0[i], true)!=NULL)));
	}
}

void Aig_ComposeVec_rec( Aig_Man_t * p, Aig_Obj_t * pObj, vector<Aig_Obj_t *>& pFuncVec,
	vector<Aig_Obj_t* >& iVarObjVec ) {
	assert( !Aig_IsComplement(pObj) );
	if ( Aig_ObjIsMarkA(pObj) )
		return;
	if ( Aig_ObjIsConst1(pObj) || Aig_ObjIsCi(pObj) ) {
		pObj->pData = pObj;
		int i = 0;
		for (auto iVarObj: iVarObjVec) {
			if(pObj == iVarObj) {
				pObj->pData = pFuncVec[i];
			}
			i++;
		}
		return;
	}
	Aig_ComposeVec_rec( p, Aig_ObjFanin0(pObj), pFuncVec, iVarObjVec );
	Aig_ComposeVec_rec( p, Aig_ObjFanin1(pObj), pFuncVec, iVarObjVec );
	pObj->pData = Aig_And( p, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
	assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
	Aig_ObjSetMarkA( pObj );
}

Aig_Obj_t * Aig_ComposeVec( Aig_Man_t * p, Aig_Obj_t * pRoot, vector<Aig_Obj_t *>& pFuncVec,
	vector<int>& iVarVec ) {
	// quit if the PI variable is not defined
	for(auto iVar: iVarVec) {
		if (iVar >= Aig_ManCiNum(p)) {
			printf( "Aig_Compose(): The PI variable %d is not defined.\n", iVar );
			return NULL;
		}
	}
	// recursively perform composition
	vector<Aig_Obj_t *> iVarObjVec(iVarVec.size());
	int i = 0;
	for (auto iVar: iVarVec) {
		iVarObjVec[i++] = Aig_ManCi(p, iVar);
	}
	Aig_ComposeVec_rec( p, Aig_Regular(pRoot), pFuncVec, iVarObjVec );
	// clear the markings
	Aig_ConeUnmark_rec( Aig_Regular(pRoot) );
	return Aig_NotCond( (Aig_Obj_t *)Aig_Regular(pRoot)->pData, Aig_IsComplement(pRoot) );
}

void Aig_VecVecConeUnmark_rec(Aig_Obj_t * pObj) {
	assert(!Aig_IsComplement(pObj));
	// cout<<"Aig_VecVecConeUnmark_rec: ";
	// Aig_ObjPrintVerbose(pObj,1);
	// cout <<endl;
	// if(Aig_ObjIsConst1(pObj) || Aig_ObjIsCi(pObj))
 //    	cout << "TOOOO111" << endl;
	if(!Aig_ObjIsMarkA(pObj))
		return;
	if(Aig_ObjIsConst1(pObj) || Aig_ObjIsCi(pObj)) {
		// cout << "TOOOO" << endl;
		delete (vector<Aig_Obj_t*> *)(pObj->pData);
		assert(Aig_ObjIsMarkA(pObj)); // loop detection
		Aig_ObjClearMarkA(pObj);
		return;
	}
	delete (vector<Aig_Obj_t*> *)(pObj->pData);
	Aig_VecVecConeUnmark_rec(Aig_ObjFanin0(pObj));
	Aig_VecVecConeUnmark_rec(Aig_ObjFanin1(pObj));
	assert(Aig_ObjIsMarkA(pObj)); // loop detection
	Aig_ObjClearMarkA(pObj);
}

void Aig_ComposeVecVec_rec(Aig_Man_t* p, Aig_Obj_t* pObj, vector<vector<Aig_Obj_t*> >& pFuncVecs) {
	assert(!Aig_IsComplement(pObj));
	if(Aig_ObjIsMarkA(pObj) )
		return;
	vector<Aig_Obj_t *>* tempData = new vector<Aig_Obj_t* >();
	if(Aig_ObjIsConst1(pObj)) {
		for(int i = 0; i < pFuncVecs.size(); i++)
			tempData->push_back(pObj);
		pObj->pData = tempData;
		assert(!Aig_ObjIsMarkA(pObj)); // loop detection
		Aig_ObjSetMarkA(pObj);
		return;
	}
	if(Aig_ObjIsCi(pObj)) {
		int i = nodeIdtoN[(pObj->Id) - 1];
		for(int j = 0; j < pFuncVecs.size(); j++)
			tempData->push_back(pFuncVecs[j][i]);
		pObj->pData = tempData;
		assert(!Aig_ObjIsMarkA(pObj)); // loop detection
		Aig_ObjSetMarkA(pObj);
		return;
	}
	Aig_ComposeVecVec_rec(p, Aig_ObjFanin0(pObj), pFuncVecs);
	Aig_ComposeVecVec_rec(p, Aig_ObjFanin1(pObj), pFuncVecs);
	for(int j = 0; j < pFuncVecs.size(); j++) {
		Aig_Obj_t *l = Aig_ObjFanin0(pObj)? Aig_NotCond(((vector<Aig_Obj_t* >*)(Aig_ObjFanin0(pObj)->pData))->at(j), Aig_ObjFaninC0(pObj)) : NULL;
		Aig_Obj_t *r = Aig_ObjFanin1(pObj)? Aig_NotCond(((vector<Aig_Obj_t* >*)(Aig_ObjFanin1(pObj)->pData))->at(j), Aig_ObjFaninC1(pObj)) : NULL;
		tempData->push_back(Aig_And(p, l, r));
	}
	pObj->pData = tempData;
	assert(!Aig_ObjIsMarkA(pObj)); // loop detection
	Aig_ObjSetMarkA(pObj);
}

vector<Aig_Obj_t* > Aig_ComposeVecVec(Aig_Man_t* p, Aig_Obj_t* pRoot,
	vector<vector<Aig_Obj_t*> >& pFuncVecs) {
	Aig_ComposeVecVec_rec(p, Aig_Regular(pRoot), pFuncVecs);
	// clear the markings
	vector<Aig_Obj_t* >* pRootpData = (vector<Aig_Obj_t* > *)(Aig_Regular(pRoot)->pData);
	int pRootIsComp = Aig_IsComplement(pRoot);
	vector<Aig_Obj_t* > result;
	for(int i = 0; i < pRootpData->size(); i++) {
		result.push_back(Aig_NotCond(pRootpData->at(i), pRootIsComp));
	}
	Aig_VecVecConeUnmark_rec(Aig_Regular(pRoot));
	return result;
}

static void Sat_SolverClauseWriteDimacs( FILE * pFile, clause * pC) {
	int i;
	for ( i = 0; i < (int)pC->size; i++ )
		fprintf( pFile, "%s%d ", (lit_sign(pC->lits[i])? "-": ""),  lit_var(pC->lits[i]));
	fprintf( pFile, "0\n" );
}

void Sat_SolverWriteDimacsAndIS(sat_solver * p, char * pFileName,
	lit* assumpBegin, lit* assumpEnd, vector<int>&IS, vector<int>&retSet) {
	Sat_Mem_t * pMem = &p->Mem;
	FILE * pFile;
	clause * c;
	int i, k, nUnits;

	// count the number of unit clauses
	nUnits = 0;
	for ( i = 0; i < p->size; i++ )
		if ( p->levels[i] == 0 && p->assigns[i] != 3 )
			nUnits++;

	// start the file
	pFile = pFileName ? fopen( pFileName, "wb" ) : stdout;
	if ( pFile == NULL )
	{
		printf( "Sat_SolverWriteDimacs(): Cannot open the ouput file.\n" );
		return;
	}

	fprintf( pFile, "p cnf %d %d\n", p->size, Sat_MemEntryNum(&p->Mem, 0)-1+Sat_MemEntryNum(&p->Mem, 1)+nUnits+(int)(assumpEnd-assumpBegin) );

	// TODO: Print Independent Support
	i=0;
	fprintf( pFile, "c ind ");
	for(auto it:IS) {
		if(i == 10) {
			fprintf( pFile, "0\nc ind ");
			i = 0;
		}
		fprintf( pFile, "%d ", it);
		i++;
	}
	fprintf( pFile, "0\n");

	// TODO: Print Return Set
	i=0;
	fprintf( pFile, "c ret ");
	for(auto it:retSet) {
		if(i == 10) {
			fprintf( pFile, "0\nc ret ");
			i = 0;
		}
		fprintf( pFile, "%d ", it);
		i++;
	}
	fprintf( pFile, "0\n");

	// write the original clauses
	Sat_MemForEachClause(pMem, c, i, k)
		Sat_SolverClauseWriteDimacs(pFile, c);

	// write the learned clauses
	Sat_MemForEachLearned(pMem, c, i, k)
		Sat_SolverClauseWriteDimacs(pFile, c);

	// write zero-level assertions
	for (i = 0; i < p->size; i++)
		if (p->levels[i] == 0 && p->assigns[i] != 3) // varX
			fprintf(pFile, "%s%d 0\n",
					(p->assigns[i] == 1)? "-": "",    // var0
					 i);

	// write the assump
	if (assumpBegin) {
		for (;assumpBegin != assumpEnd; assumpBegin++) {
			fprintf( pFile, "%s%d 0\n",
					 lit_sign(*assumpBegin)? "-": "",
					 lit_var(*assumpBegin));
		}
	}

	fprintf(pFile, "\n");
	if (pFileName) fclose(pFile);
}

void* unigenCallThread(void* i) {
	auto start = std::chrono::steady_clock::now();
	pthread_mutex_lock(&CMSat::mu_lock);
	CMSat::CUSP::unigenRunning = true;
	pthread_mutex_unlock(&CMSat::mu_lock);

	CMSat::CUSP unigenCall(unigen_argc, unigen_argv);
	unigenCall.conf.verbStats = 1;
	unigenCall.parseCommandLine();
	unigenCall.solve();

	pthread_mutex_lock(&CMSat::mu_lock);
	CMSat::CUSP::unigenRunning = false;
	pthread_cond_signal(&CMSat::lilCondVar);
	pthread_mutex_unlock(&CMSat::mu_lock);
	unigen_threadId = -1;
	auto end = std::chrono::steady_clock::now();
	sat_solving_time += std::chrono::duration_cast<std::chrono::microseconds>(end - start).count()/1000000.0;
	pthread_exit(NULL);
}


/**Function
 * returns 0  when unsat
 * returns -1 when sat but number of solutions is too small
 * returns  1 when sat and models succesfully populated UNIGEN_MODEL_FPATH
 */
int unigen_call(string fname, int nSamples, int nThreads) {
	numUnigenCalls++;
	assert(fname.find(' ') == string::npos);
	system("rm -rf " UNIGEN_OUT_DIR "/*");

	unigen_argv[unigen_samples_argnum] = (char*)((new string("--samples="+to_string(nSamples)))->c_str());
	unigen_argv[unigen_threads_argnum] = (char*)((new string("--threads="+to_string(nThreads)))->c_str());
	unigen_argv[unigen_cnfname_argnum] = (char*)((new string(fname))->c_str());

	string cmd;
	for (int i = 0; i < unigen_argc; ++i) {
		cmd = cmd + string(unigen_argv[i]) + " ";
	}
	cout << "\nCalling unigen: " << cmd << endl;
	cout << "Fresh PACratios hereon" << endl;


	// Initializations
	CMSat::CUSP::prematureKill = false;
	CMSat::CUSP::firstFetch    = true;
	CMSat::CUSP::initStat = CMSat::initialStatus::udef;
	CMSat::CUSP::unigenCalledAt = chrono::steady_clock::now();
	cexSeen.clear();

	// Thread Creation
	assert(!pthread_create(&unigen_threadId, NULL, unigenCallThread, NULL));
	if(!options.unigenBackground)
		pthread_join(unigen_threadId, NULL);

	pthread_mutex_lock(&CMSat::stat_lock);
	while(CMSat::CUSP::initStat == CMSat::initialStatus::udef)
		pthread_cond_wait(&CMSat::statCondVar, &CMSat::stat_lock);
	pthread_mutex_unlock(&CMSat::stat_lock);

	printf("ApproxMC #CEX (Sci.):   =%d*2^%d\n", CMSat::CUSP::approxmcBase, CMSat::CUSP::approxmcExpo);
	printf("ApproxMC #CEX (Dec.):   %f\n", CMSat::CUSP::approxmcBase*pow(2.0,CMSat::CUSP::approxmcExpo));
	printf("Badness Ratio (Sci.):   =%d*2^%d\n", CMSat::CUSP::approxmcBase, CMSat::CUSP::approxmcExpo - numX);
	printf("Badness Ratio (Dec.):   %f\n", CMSat::CUSP::approxmcBase*pow(2.0,CMSat::CUSP::approxmcExpo - numX));

	switch(CMSat::CUSP::initStat) {
		case CMSat::initialStatus::unsat: return 0;
		case CMSat::initialStatus::tooLittle: return -1;
		case CMSat::initialStatus::sat:
			if(options.checkSatOnly) {
				cout << "SAT, Terminating Unigen prematurely" << endl;
				CMSat::CUSP::prematureKill = true;
				pthread_join(unigen_threadId, NULL);

				pthread_mutex_lock(&CMSat::mu_lock);
				CMSat::CUSP::unigenRunning = false;
				pthread_cond_signal(&CMSat::lilCondVar);
				pthread_mutex_unlock(&CMSat::mu_lock);
				unigen_threadId = -1;

				exit(0);
			}
		return 1;
	}

	// control cannot reach here
	assert(false);
}

bool unigen_fetchModels(Aig_Man_t* SAig, vector<vector<int> > &r0,
	vector<vector<int> > &r1, bool more) {

	bool flag = false;
	string line;
	auto storedSolutionMap = CMSat::CUSP::fetchSolutionMap(options.waitSamples);
	solsJustFetched = 0;
	for(auto it:storedSolutionMap) {
		line = it.first;
		if(line == " " || line == "")
			continue;

		solsJustFetched++;

		int startPoint = (line[0] == ' ') ? 2 : 1;
		line = line.substr(startPoint, line.size() - 2 - startPoint);
		if(cexSeen.find(line) != cexSeen.end())
			continue;
		else
			cexSeen[line] = 1;

		istringstream iss(line);

		vector<int> cex(2*numOrigInputs,-1);
		vector<int> r0Andr1Vars(numY);
		for(int it; iss >> it; ) {
			int modelVal = it;
			auto itID = varNum2ID.find(abs(modelVal));
			if(itID != varNum2ID.end()) {
				cex[itID->second] = (modelVal > 0) ? 1 : 0;
			}
			else {
				auto itR0R1 = varNum2R0R1.find(abs(modelVal));
				assert(itR0R1 != varNum2R0R1.end());
				r0Andr1Vars[itR0R1->second] = (modelVal > 0) ? 1 : 0;
			}
		}
		// Sanity Check
		for(int i = 0; i<numX; i++)
			assert(cex[numOrigInputs+i]==-1);

		// find k1
		int k1 = numY-1;
		while(r0Andr1Vars[k1] == 0) {k1--;}
		assert(k1 >= 0);

		storedCEX.push_back(cex);
		storedCEX_k1.push_back(more?-1:k1);
		storedCEX_k2.push_back(-1);
		storedCEX_unused.push_back(true);
		storedCEX_r0Sat.push_back(vector<bool>(numY, false));
		storedCEX_r1Sat.push_back(vector<bool>(numY, false));
		flag = true;
	}
	cout << "storedCEX.size() = " << storedCEX.size() << endl;

	return flag;
}

vector<lit> setAllNegX(Cnf_Dat_t* SCnf, Aig_Man_t* SAig, int val) {
	vector<lit> res(numX);
	for (int i = 0; i < numX; ++i) {
		res[i] = toLitCond(SCnf->pVarNums[numOrigInputs + varsXS[i]], (int) val==0);
	}
	return res;
}

int filterAndPopulateK1Vec(Aig_Man_t* SAig, vector<vector<int> >&r0, vector<vector<int> >&r1, int prevM) {
	int k = -1;
	int max = -1;
	Aig_Obj_t *mu0, *mu1;
	vector<bool> spurious(storedCEX.size(),1);
	int index = 0;

	// cout << "POPULATING K1 VECTOR" << endl;
	assert(storedCEX_k1.size() == storedCEX.size());

	int maxChange = (prevM==-1)? (numY-1) : (prevM+1);

	for(auto& cex:storedCEX) {
		assert(cex.size() == 2*numOrigInputs);
		if( options.useFmcadPhase or
			((prevM != -1 and storedCEX_k2[index] == prevM) ||
			(storedCEX_k1[index] == -1))) {
			for (int i = maxChange; i >= 0; --i) {
				evaluateAig(SAig,cex);
				vector<int>& r_ = useR1AsSkolem[i]?r1[i]:r0[i];
				bool r_i = false;
				for(auto r_El: r_) {
					if(Aig_ManCo(SAig, r_El)->iData == 1) {
						r_i = true;
						break;
					}
				}
				cex[numX + i] = (int) (useR1AsSkolem[i] ^ r_i);
			}
			evaluateAig(SAig, cex);
			spurious[index] = (bool)(Aig_ManCo(SAig, F_SAigIndex)->iData != 1);

			if(spurious[index]) {
				int k_max = (storedCEX_k2[index]==-1)?numY-1:storedCEX_k2[index];
				for(k = k_max; k >= 0; k--) {
					storedCEX_r1Sat[index][k] = ((mu1 = satisfiesVec(SAig, cex, r1[k], false)) != NULL);
					storedCEX_r0Sat[index][k] = ((mu0 = satisfiesVec(SAig, cex, r0[k], false)) != NULL);
					if(storedCEX_r1Sat[index][k] and storedCEX_r0Sat[index][k])
						break;
				}
				storedCEX_k1[index] = k;
			}
		}

		if(spurious[index])
			max = (storedCEX_k1[index] > max) ? storedCEX_k1[index] : max;

		index++;
	}

	int j = 0;
	for(int i = 0; i < storedCEX.size(); i++) {
		if(spurious[i]) {
			storedCEX[j] = storedCEX[i];
			storedCEX_k1[j] = storedCEX_k1[i];
			storedCEX_k2[j] = storedCEX_k2[i];
			storedCEX_unused[j] = storedCEX_unused[i];
			storedCEX_r0Sat[j] = storedCEX_r0Sat[i];
			storedCEX_r1Sat[j] = storedCEX_r1Sat[i];
			j++;
		}
	}
	storedCEX.resize(j);
	storedCEX_k1.resize(j,-1);
	storedCEX_k2.resize(j,-1);
	storedCEX_unused.resize(j,false);
	storedCEX_r0Sat.resize(j,vector<bool>(numY, false));
	storedCEX_r1Sat.resize(j,vector<bool>(numY, false));
	assert(max>=0 || j==0);
	return max;
}

int filterAndPopulateK1VecFast(Aig_Man_t* SAig, vector<vector<int> >&r0, vector<vector<int> >&r1, int prevM) {
	int k1;
	int max = -1;
	Aig_Obj_t *mu0, *mu1;
	vector<bool> spurious(storedCEX.size(),1);
	int index = 0;

	// cout << "POPULATING K1 VECTOR" << endl;
	assert(storedCEX_k1.size() == storedCEX.size());

	int maxChange = (prevM==-1)? (numY-1) : (prevM+1);

	for(auto& cex:storedCEX) {
		assert(cex.size() == 2*numOrigInputs);

		if(options.useFmcadPhase or
			((prevM != -1 and storedCEX_k2[index] == prevM) ||
			(storedCEX_k1[index] == -1))) {

			// New algo
			evaluateXYLeaves(SAig,cex);
			// Re-evaluating some Ys
			for (int i = maxChange; i >= 0; --i) {
				vector<int>& r_ = useR1AsSkolem[i]?r1[i]:r0[i];
				bool r_i = false;
				for(auto r_El: r_) {
					if(evaluateAigAtNode(SAig,Aig_ManCo(SAig, r_El))) {
						r_i = true;
						break;
					}
				}
				cex[numX + i] = (int) (useR1AsSkolem[i] ^ r_i);
				Aig_ManObj(SAig, varsYS[i])->iData = cex[numX + i];
			}
			spurious[index] = !evaluateAigAtNode(SAig,Aig_ManCo(SAig, F_SAigIndex));

			if(spurious[index]) {
				int k1_maxLim = (storedCEX_k2[index]==-1)?numY-1:storedCEX_k2[index];
				for(k1 = k1_maxLim; k1 >= 0; k1--) {
					// Check if r1[k1] is true
					bool r1i = false;
					for(auto r1El: r1[k1]) {
						if(evaluateAigAtNode(SAig,Aig_ManCo(SAig, r1El))) {
							r1i = true; break;
						}
					}
					storedCEX_r1Sat[index][k1] = r1i;
					// Check if r0[k1] is true
					bool r0i = false;
					for(auto r0El: r0[k1]) {
						if(evaluateAigAtNode(SAig,Aig_ManCo(SAig, r0El))) {
							r0i = true; break;
						}
					}
					storedCEX_r0Sat[index][k1] = r0i;
					if(r0i and r1i) break;
				}
				storedCEX_k1[index] = k1;
			}
			Aig_ManIncrementTravId(SAig);
		}

		if(spurious[index])
			max = (storedCEX_k1[index] > max) ? storedCEX_k1[index] : max;

		index++;
	}

	int j = 0;
	for(int i = 0; i < storedCEX.size(); i++) {
		if(spurious[i]) {
			storedCEX[j] = storedCEX[i];
			storedCEX_k1[j] = storedCEX_k1[i];
			storedCEX_k2[j] = storedCEX_k2[i];
			storedCEX_unused[j] = storedCEX_unused[i];
			storedCEX_r0Sat[j] = storedCEX_r0Sat[i];
			storedCEX_r1Sat[j] = storedCEX_r1Sat[i];
			j++;
		}
	}
	storedCEX.resize(j);
	storedCEX_k1.resize(j,-1);
	storedCEX_k2.resize(j,-1);
	storedCEX_unused.resize(j,false);
	storedCEX_r0Sat.resize(j,vector<bool>(numY, false));
	storedCEX_r1Sat.resize(j,vector<bool>(numY, false));

	assert(max>=0 || j==0);
	return max;
}

int populateK2Vec(Aig_Man_t* SAig, vector<vector<int> >&r0, vector<vector<int> >&r1, int prevM) {
	int k1;
	int k2;
	int k2_prev;
	int i = 0;
	int max = -1;

	// cout << "POPULATING K2 VECTOR" << endl;
	assert(storedCEX_k2.size() == storedCEX.size());
	for(auto cex:storedCEX) {
		k2 = storedCEX_k2[i];
		// TODO the if statements
		if(options.useFmcadPhase or
			(k2 == -1 or k2 == prevM)) { // Change only if k2 == prevM
			int clock1 = clock();
			k2_prev = k2;
			k1 = storedCEX_k1[i];
			int k2Lim = (k2==-1)?numY - 1:k2+1;
			// cout << "Finding k2..." << endl;
			// cout << "Search range from " << k1 << " to " << k2Lim << endl;
			int k2_actual = findK2Max(SAig, m_pSat, m_FCnf, cex, r0, r1, k1, numY - 1);
			// cout << "k2_actual: " << k2_actual  << endl;
			k2 = findK2Max(SAig, m_pSat, m_FCnf, cex, r0, r1, k1, k2Lim);
			// cout << "k2:        " << k2 << endl;
			assert(k2_actual == k2);
			clock1 = clock() - clock1;
			// printf ("Found k2 = %d, took (%f seconds)\n",k2,((float)clock1)/CLOCKS_PER_SEC);
			storedCEX_k2[i] = k2;
			assert(k2>=k1);
			k2Trend[(k2_prev==-1)?numY:k2_prev][k2]++;
		}
		max = (k2 > max) ? k2 : max;
		i++;
	}

	return max;
}

int findK2Max(Aig_Man_t* SAig, sat_solver* m_pSat, Cnf_Dat_t* m_FCnf, vector<int>&cex,
	vector<vector<int> >&r0, vector<vector<int> >&r1, int k1, int prevM) {

	Aig_Obj_t *mu0, *mu1, *mu, *pAigObj;
	int return_val;

	lit assump[numOrigInputs + 1];
	assump[0] = m_f;

	// push X values
	for (int i = 0; i < numX; ++i) {
		assump[i + 1] = toLitCond(m_FCnf->pVarNums[varsXS[i]], (int)cex[i]==0);
	}

	int k_end = (prevM==-1)?numY-1:prevM;
	return_val = findK2Max_rec(m_pSat, m_FCnf, cex, k1 + 1, k_end, assump);

	return return_val;
}

// INV: k_end => SAT; k_start-1=> UNSAT
int findK2Max_rec(sat_solver* pSat, Cnf_Dat_t* SCnf, vector<int>&cex,
		int k_start, int k_end, lit assump[]) {
	// printf("findK2Max_rec(%d,%d)\n", k_start, k_end);
	assert(k_start <= k_end);
	if(k_start == k_end)
		return k_start - 1;
	if(k_start + 1 == k_end)
		if(checkIsFUnsat(pSat, SCnf, cex, k_start, assump))
			return k_start;
		else
			return k_start - 1;

	int k_mid = (k_start + k_end)/2;
	if(checkIsFUnsat(pSat,SCnf,cex, k_mid, assump)) { // going right
		return findK2Max_rec(pSat, SCnf, cex, k_mid + 1, k_end, assump);
	} else {
		return findK2Max_rec(pSat, SCnf, cex, k_start, k_mid, assump);
	}
}

bool checkIsFUnsat(sat_solver* pSat, Cnf_Dat_t* SCnf, vector<int>&cex,
		int k, lit assump[]) {
	// cout << "SAT call, check for k2 = " << k << endl;
	// printf("checkIsFUnsat(%d)\n",k);
	assert(k < numY);
	if(k == numY - 1)
		return false;
	if(k == 0)
		return true;
	// sat_solver_bookmark(pSat);

	// Push counterexamples from k+1 till numY-1 (excluded)
	for (int i = numY - 1; i > k; --i) {
		assump[numOrigInputs - i] = toLitCond(SCnf->pVarNums[varsYS[i]],(int)cex[numX + i]==0);
	}

	if(!sat_solver_simplify(pSat)) {
		// cout << "Trivially unsat" << endl;
		return true;
	}

	int clock1 = clock();
	int status = sat_solver_solve(pSat, assump, assump + (numOrigInputs - k),
					(ABC_INT64_T)0, (ABC_INT64_T)0,
					(ABC_INT64_T)0, (ABC_INT64_T)0);
	clock1 = clock() - clock1;
	// printf ("Time SAT call (%f s) ",((float)clock1)/CLOCKS_PER_SEC);

	if (status == l_False) {
		// cout << "returned unsat" << endl;
		return true;
	}
	else {
		assert(status == l_True);
		// cout << "returned sat" << endl;
		return false;
	}
}

void initializeAddR1R0toR() {
	addR1R0toR0 = vector<bool>(numY,true);
	addR1R0toR1 = vector<bool>(numY,true);
	collapsedInto = vector<bool>(numY,false);
}

void collapseInitialLevels(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1) {
	cout << "collapseInitialLevels" << endl;
	Aig_Obj_t *mu0, *mu1, *mu;
	for(int i = 0; i<options.c1; i++) {
		mu0 = newOR(pMan, r0[i]);
		mu1 = newOR(pMan, r1[i]);
		mu = Aig_AndAigs(pMan, mu0, mu1);

		mu1 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 1);
		Aig_ObjCreateCo(pMan, mu1);
		r1[i+1].push_back(Aig_ManCoNum(pMan) - 1);
		addR1R0toR1[i] = false;

		mu0 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 0);
		Aig_ObjCreateCo(pMan, mu0);
		r0[i+1].push_back(Aig_ManCoNum(pMan) - 1);
		addR1R0toR0[i] = false;
	}
}

void propagateR1Cofactors(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1) {
	cout << "propagateR1Cofactors" << endl;
	Aig_Obj_t *mu0, *mu1, *mu;

	for(int i = 0; i<numY-1; i++) {
		mu0 = newOR(pMan, r0[i]);
		mu1 = newOR(pMan, r1[i]);
		mu = Aig_AndAigs(pMan, mu0, mu1);

		mu1 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 1);
		Aig_ObjCreateCo(pMan, mu1);
		r1[i+1].push_back(Aig_ManCoNum(pMan) - 1);

		addR1R0toR1[i] = false;
	}
}

void propagateR0Cofactors(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1) {
	cout << "propagateR0Cofactors" << endl;
	Aig_Obj_t *mu0, *mu1, *mu;

	for(int i = 0; i<numY-1; i++) {
		mu0 = newOR(pMan, r0[i]);
		mu1 = newOR(pMan, r1[i]);
		mu = Aig_AndAigs(pMan, mu0, mu1);

		mu0 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 0);
		Aig_ObjCreateCo(pMan, mu0);
		r0[i+1].push_back(Aig_ManCoNum(pMan) - 1);

		addR1R0toR0[i] = false;
	}
}

void propagateR_Cofactors(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1) {
	cout << "propagateR_Cofactors" << endl;
	Aig_Obj_t *mu0, *mu1, *mu;

	for(int i = 0; i<numY-1; i++) {
		mu0 = newOR(pMan, r0[i]);
		mu1 = newOR(pMan, r1[i]);
		mu = Aig_AndAigs(pMan, mu0, mu1);

		if(useR1AsSkolem[i+1]) {
			mu1 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 1);
			Aig_ObjCreateCo(pMan, mu1);
			r1[i+1].push_back(Aig_ManCoNum(pMan) - 1);
			addR1R0toR1[i] = false;
		}
		else {
			mu0 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 0);
			Aig_ObjCreateCo(pMan, mu0);
			r0[i+1].push_back(Aig_ManCoNum(pMan) - 1);
			addR1R0toR0[i] = false;
		}
	}
}

void propagateR0R1Cofactors(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1) {
	cout << "propagateR0R1Cofactors" << endl;
	Aig_Obj_t *mu0, *mu1, *mu;
	vector<int> r0Addn(numY);
	vector<int> r1Addn(numY);

	for(int i = 0; i<numY-1; i++) {
		mu0 = newOR(pMan, r0[i]);
		mu1 = newOR(pMan, r1[i]);
		mu = Aig_AndAigs(pMan, mu0, mu1);

		mu1 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 1);
		Aig_ObjCreateCo(pMan, mu1);
		r1Addn[i+1] = Aig_ManCoNum(pMan) - 1;

		mu0 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 0);
		Aig_ObjCreateCo(pMan, mu0);
		r0Addn[i+1] = Aig_ManCoNum(pMan) - 1;
	}

	addR1R0toR1[0] = false;
	addR1R0toR0[0] = false;

	for(int i = 1; i<numY; i++) {
		r1[i].push_back(r1Addn[i]);
		r0[i].push_back(r0Addn[i]);
	}
}

void chooseSmallerR_(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1) {
	clock_t start = clock();

	cout << "Skolem Choices: " << endl;
	for (int i = 0; i < numY; ++i) {
		int sizeR1 = Aig_DagSize(newOR(pMan, r1[i]));
		int sizeR0 = Aig_DagSize(newOR(pMan, r0[i]));
		useR1AsSkolem[i] = sizeR1 < sizeR0;
		cout << useR1AsSkolem[i] << " ";
	}
	cout << endl;

	clock_t end = clock();
	cout << "Time taken = " << double( end-start)/CLOCKS_PER_SEC << endl;
}

void chooseR_(Aig_Man_t* pMan, vector<vector<int> >& r0, vector<vector<int> >& r1) {
	if(options.skolemType == sType::skolemR0) {
		cout << "Choosing r0 as Skolem" << endl;
		useR1AsSkolem = vector<bool>(numY,false);
	}
	else if(options.skolemType == sType::skolemR1) {
		cout << "Choosing ~r1 as Skolem" << endl;
		useR1AsSkolem = vector<bool>(numY,true);
	}
	else {
		cout << "Choosing smaller of r0/r1 as Skolem" << endl;
		chooseSmallerR_(pMan, r0, r1);
	}
}

void printK2Trend() {
	int totalSum = 0;
	cout << "k2Trend:" << endl;
	cout << "\t";
	for (int j = numY-1; j >= 0; --j) {
		cout << "Y" << j << "\t";
	}
	cout << "Sum" << endl;
	for (int i = numY; i >= 0; --i) {
		int rowSum = 0;
		if(i == numY)
			cout << "Init" << "\t";
		else
			cout << "Y" << i << "\t";
		for (int j = numY-1; j >= 0; --j) {
			cout << k2Trend[i][j] << "\t";
			rowSum += k2Trend[i][j];
		}
		cout << rowSum << endl;
		totalSum += rowSum;
	}
	cout << "Sum\t";
	for (int i = numY-1; i >= 0; --i) {
		int colSum = 0;
		for (int j = numY; j >= 0; --j) {
			colSum += k2Trend[j][i];
		}
		cout << colSum << "\t";
	}
	cout << totalSum << endl << endl;
}

void monoSkolem(Aig_Man_t*&pMan, vector<vector<int> > &r0, vector<vector<int> > &r1) {
	cout << "Running MonoSkolem" << endl;
	Aig_Obj_t *mu0, *mu1, *mu, *pAigObj;

	for(int i = 0; i<numY-1; i++) {
		mu0 = newOR(pMan, r0[i]);
		mu1 = newOR(pMan, r1[i]);
		mu = Aig_AndAigs(pMan, mu0, mu1);

		mu1 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 1);
		pAigObj = Aig_ManCo(pMan,r1[i+1][0]);
		Aig_ObjPatchFanin0(pMan, pAigObj, mu1);

		mu0 = Aig_SubstituteConst(pMan, mu, varsYS[i+1], 0);
		pAigObj = Aig_ManCo(pMan,r0[i+1][0]);
		Aig_ObjPatchFanin0(pMan, pAigObj, mu0);
	}

	return;
}

string getFileName(string s) {
	size_t i;

	i = s.rfind('/', s.length());
	if (i != string::npos) {
		s = s.substr(i+1);
	}
	assert(s.length() != 0);

	i = s.rfind('.', s.length());
	if (i != string::npos) {
		s = s.substr(0,i);
	}
	assert(s.length() != 0);

	return(s);
}

int checkUnateSyntacticAll(Aig_Man_t* FAig, vector<int>&unate) {
	Nnf_Man nnfSyntatic(FAig);
	assert(nnfSyntatic.getCiNum() == numOrigInputs);

	int numUnate = 0;
	for(int i = 0; i < numY; ++i) {
		if (unate[i] == -1) {
			int refPos = nnfSyntatic.getCiPos(varsYF[i] - 1)->getNumRef();
			int refNeg = nnfSyntatic.getCiNeg(varsYF[i] - 1)->getNumRef();
			if(refPos == 0) {
				unate[i] = 0;
				cout << "Var y" << i << " (" << varsYF[i] << ") is negative unate (syntactic)" << endl;
			} else if(refNeg == 0) {
				unate[i] = 1;
				cout << "Var y" << i << " (" << varsYF[i] << ") is positive unate (syntactic)" << endl;
			}
			if (unate[i] != -1) {
				numUnate++;
			}
		}
	}
	cout << "Found " << numUnate << " unates" << endl;
	return numUnate;
}

// skolems[] = 1 (pos unate); 0 (neg unate); -1 (not unate)
int checkUnateSemanticAll(Aig_Man_t* FAig, vector<int>&unate) {
	Aig_ManPrintStats(FAig);

	auto unate_start = std::chrono::steady_clock::now();
	auto unate_end = std::chrono::steady_clock::now();
	auto unate_run_time = std::chrono::duration_cast<std::chrono::microseconds>(unate_end - unate_start).count()/1000000.0;

	nodeIdtoN.resize(numOrigInputs);
	for(int i = 0; i < numX; i++) {
		nodeIdtoN[varsXF[i] - 1] = i;
	}
	for(int i = 0; i < numY; i++) {
		nodeIdtoN[varsYF[i] - 1] = numX + i;
	}

	vector<vector<Aig_Obj_t* > > funcVecVec;
	vector<Aig_Obj_t* > retVec;
	vector<Aig_Obj_t* > funcVec;
	vector<Aig_Obj_t* > funcVecTemp;

	funcVecTemp.resize(0);
	for(int i = 0; i < numX; ++i) {
		funcVecTemp.push_back(Aig_ManObj(FAig, varsXF[i]));
	}
	for(int i = 0; i < numY; ++i) {
		funcVecTemp.push_back(Aig_ManObj(FAig, varsYF[i]));
	}

	for (int i = 0; i < numY; ++i) {
		funcVec = funcVecTemp;
		funcVec[numX+i] = Aig_ManConst0(FAig);
		funcVecVec.push_back(funcVec);
		funcVec[numX+i] = Aig_ManConst1(FAig);
		funcVecVec.push_back(funcVec);
	}

	retVec = Aig_SubstituteVecVec(FAig, Aig_ManCo(FAig, 0), funcVecVec);

	vector<int> posUnates;
	vector<int> negUnates;
	for (int i = 0; i < numY; ++i)
	{
		// pos unate
		auto posUnateNode = Aig_OrAigs(FAig, Aig_Not(retVec[2*i]), retVec[2*i+1]);
		Aig_ObjCreateCo(FAig, posUnateNode);
		posUnates.push_back(Aig_ManCoNum(FAig) - 1);

		// neg unate
		auto negUnateNode = Aig_OrAigs(FAig, retVec[2*i], Aig_Not(retVec[2*i+1]));
		Aig_ObjCreateCo(FAig, negUnateNode);
		negUnates.push_back(Aig_ManCoNum(FAig) - 1);
	}

	// Build Solver and CNF
	sat_solver* pSat = sat_solver_new();
	Cnf_Dat_t* SCnf = Cnf_Derive(FAig, Aig_ManCoNum(FAig));
	addCnfToSolver(pSat, SCnf);

	int status, numUnate, totalNumUnate = 0;
	assert(unate.size()==numY);

	// Unate Sat Calls
	do {
		numUnate = 0;
		for (int i = 0; i < numY; ++i)
		{
			lit LA[2];

			if(unate[i] == -1) {
				// Check if positive unate
				LA[0] = toLitCond(getCnfCoVarNum(SCnf, FAig, posUnates[i]),1);
				status = sat_solver_solve(pSat, LA, LA+1, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
				if (status == l_False) {
					unate[i] = 1;
					cout << "Var y" << i << " (" << varsYF[i] << ") is positive unate (semantic)" << endl;
					// sat_solver_push(pSat, toLitCond(SCnf->pVarNums[varsYF[i]],0));
					addVarToSolver(pSat, SCnf->pVarNums[varsYF[i]], 1);
					numUnate++;
				}
			}

			if(unate[i] == -1) {
				// Check if negative unate
				LA[0] = toLitCond(getCnfCoVarNum(SCnf, FAig, negUnates[i]),1);
				status = sat_solver_solve(pSat, LA, LA+1, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
				if (status == l_False) {
					cout << "Var y" << i << " (" << varsYF[i] << ") is negative unate (semantic)" << endl;
					unate[i] = 0;
					// sat_solver_push(pSat, toLitCond(SCnf->pVarNums[varsYF[i]],1));
					addVarToSolver(pSat, SCnf->pVarNums[varsYF[i]], 0);
					numUnate++;
				}
			}
		}
		cout << "Found " << numUnate << " unates" << endl;
		totalNumUnate += numUnate;

		unate_end = std::chrono::steady_clock::now();
		unate_run_time = std::chrono::duration_cast<std::chrono::microseconds>(unate_end - main_time_start).count()/1000000.0;
		if(numUnate > 0 and unate_run_time >= options.unateTimeout) {
			cout << "checkUnateSemanticAll Timed Out" << endl;
			break;
		}
	}
	while(numUnate > 0);

	sat_solver_delete(pSat);
	Cnf_DataFree(SCnf);

	return totalNumUnate;
}

void populateVars(Abc_Ntk_t* FNtk, string varsFile,
	vector<int>& varsXF, vector<int>& varsYF,
	map<string,int>& name2IdF, map<int,string>& id2NameF) {

	int i;
	Abc_Obj_t* pPi;
	string line;

	Abc_NtkForEachCi( FNtk, pPi, i ) {
		string variable_name = Abc_ObjName(pPi);
		name2IdF[variable_name] = pPi->Id;
	}

	for(auto it:name2IdF)
		id2NameF[it.second] = it.first;

	auto name2IdFTemp = name2IdF;
	ifstream varsStream(varsFile);
	if(!varsStream.is_open()) {
		cout << "Var File " + varsFile + " does not exist!" << endl;
		cerr << "Var File " + varsFile + " does not exist!" << endl;
	}
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

	numX = varsXF.size();
	numY = varsYF.size();
	numOrigInputs = numX + numY;

	if(numY <= 0) {
		cout << "Var File " + varsFile + " is empty!" << endl;
		cerr << "Var File " + varsFile + " is empty!" << endl;
		assert(numY > 0);
	}
}

void substituteUnates(Aig_Man_t* &pMan, vector<int>&unate) {
	// Delete other COs
	while(Aig_ManCoNum(pMan) > 1) {
		Aig_ObjDeleteCo(pMan, Aig_ManCo(pMan,1));
	}
	Aig_ManCleanup(pMan);

	// Substitute
	vector<int> varIdVec;
	vector<Aig_Obj_t*> funcVec;
	for (int i = 0; i < numY; ++i) {
		if(unate[i] == 1) {
			varIdVec.push_back(varsYF[i]);
			funcVec.push_back(Aig_ManConst1(pMan));
		}
		else if(unate[i] == 0) {
			varIdVec.push_back(varsYF[i]);
			funcVec.push_back(Aig_ManConst0(pMan));
		}
	}
	Aig_Obj_t* pAigObj = Aig_SubstituteVec(pMan, Aig_ManCo(pMan,0), varIdVec, funcVec);
	Aig_ObjPatchFanin0(pMan, Aig_ManCo(pMan,0), pAigObj);
	Aig_ManCleanup(pMan);

	// Duplicate Aig to toposort nodes
	Aig_Man_t* tempAig = pMan;
	pMan = Aig_ManDupSimple(pMan);
	Aig_ManStop(tempAig);
}

// Assumes skolemAig[...] correspond to varsYS[...]
void saveSkolems(Aig_Man_t* SAig, vector<int>& skolemAig) {
	assert(skolemAig.size() == numY);

	// // Checking Supports for all except X
	// cout << "Checking Support in saveSkolems" << endl;
	// vector<int> temp = varsXS;
	// sort(temp.begin(), temp.end());
	// int k = 0;
	// for (int j = 1; j <= Aig_ManCiNum(SAig); ++j) {
	// 	while(j==temp[k] and k<temp.size() and j <= Aig_ManCiNum(SAig)) {
	// 		j++;
	// 		k++;
	// 	}
	// 	for (int i = 0; i < numY; ++i) {
	// 		assert(Aig_Support(SAig, Aig_ManCo(SAig, skolemAig[i]), j) == false);
	// 	}
	// }

	int i;
	Abc_Obj_t* pObj;

	// Specify Ci/Co to pick
	Vec_Ptr_t * vPis = Vec_PtrAlloc(numX);
	Vec_Ptr_t * vPos = Vec_PtrAlloc(numY);
	for(auto it:varsXS) {
		Vec_PtrPush(vPis, Aig_ManObj(SAig,it));
	}
	for(auto it:skolemAig) {
		Vec_PtrPush(vPos, Aig_ManCo(SAig,it));
	}

	// Get partial Aig, Ntk
	Aig_Man_t* outAig = Aig_ManDupSimpleDfsPart(SAig, vPis, vPos);
	Abc_Ntk_t* outNtk = Abc_NtkFromAigPhase(outAig);

	// Unset and Set Input, Output Names
	string ntkName = getFileName(options.benchmark)+"_skolem";
	Abc_NtkSetName(outNtk, Abc_UtilStrsav((char*)(ntkName).c_str()));
	Nm_ManFree(outNtk->pManName);
	outNtk->pManName = Nm_ManCreate(200);

	Abc_NtkForEachCi(outNtk, pObj, i) {
		Abc_ObjAssignName(pObj, (char*)varsNameX[i].c_str(), NULL);
	}
	Abc_NtkForEachCo(outNtk, pObj, i) {
		Abc_ObjAssignName(pObj, (char*)varsNameY[i].c_str(), NULL);
	}

	// Write to verilog
	Abc_FrameSetCurrentNetwork(pAbc, outNtk);
	string command = "write "+options.outFName;
	if (Cmd_CommandExecute(pAbc, (char*)command.c_str())) {
		cerr << "Could not write result to verilog file" << endl;
	}
	else {
		cout << "Saved skolems to " << options.outFName << endl;
	}
}

void printAig(Aig_Man_t* pMan) {
	int i;
	Aig_Obj_t* pAigObj;
	cout << "\nAig: " << endl;
	Aig_ManForEachObj( pMan, pAigObj, i )
	    Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
	cout << endl;
}

int Aig_ConeCountWithConstAndMark_rec( Aig_Obj_t * pObj ) {
    int Counter;
    assert( !Aig_IsComplement(pObj) );
    if (!Aig_ObjIsNode(pObj) || Aig_ObjIsMarkA(pObj) )
    {
		if (Aig_ObjIsConst1(pObj) || Aig_ObjIsCi(pObj)) {
			if(Aig_ObjIsMarkA(pObj))
				return 0;
			else {
				Aig_ObjSetMarkA( pObj );
				return 1;
			}
		}
		else
	        return 0;
    }
    Counter = 1 + Aig_ConeCountWithConstAndMark_rec( Aig_ObjFanin0(pObj) ) +
        Aig_ConeCountWithConstAndMark_rec( Aig_ObjFanin1(pObj) );
    assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjSetMarkA( pObj );
    return Counter;
}

void Aig_ConeWithConstUnmark_rec( Aig_Obj_t * pObj ) {
    assert( !Aig_IsComplement(pObj) );
    if ( !Aig_ObjIsNode(pObj) || !Aig_ObjIsMarkA(pObj) )
    {
		if (Aig_ObjIsConst1(pObj)|| Aig_ObjIsCi(pObj))
			Aig_ObjClearMarkA( pObj );
	    return;
    }
    Aig_ConeWithConstUnmark_rec( Aig_ObjFanin0(pObj) );
    Aig_ConeWithConstUnmark_rec( Aig_ObjFanin1(pObj) );
    assert( Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjClearMarkA( pObj );
}

int Aig_DagSizeWithConst( Aig_Obj_t * pObj ) {
    int Counter;
    Counter = Aig_ConeCountWithConstAndMark_rec( Aig_Regular(pObj) );
    Aig_ConeWithConstUnmark_rec( Aig_Regular(pObj) );
    return Counter;
}

void printBDDNode(DdManager* ddMan, DdNode* obj) {
	assert(!Cudd_IsComplement(obj));
	printf("Node %d : ", obj->Id);

	if (Cudd_IsConstant(obj))
		printf("constant %f", Cudd_V(obj));
	else
		printf("ite(v%d, %d%s, %d%s)", obj->index,
			Cudd_Regular(Cudd_T(obj))->Id, (Cudd_IsComplement(Cudd_T(obj))? "\'" : " "),
			Cudd_Regular(Cudd_E(obj))->Id, (Cudd_IsComplement(Cudd_E(obj))? "\'" : " "));

	printf(" (refs = %3d)\n", obj->ref);
}

void printBDD(DdManager* ddMan, DdNode* f) {
	DdGen *gen;
	DdNode *node;
	Cudd_ForeachNode(ddMan, f, gen, node) {
		printBDDNode(ddMan, node);
	}
}
