#include <bits/stdc++.h>
#include "helper.h"

#define ABC_NAMESPACE NS_ABC

using namespace std;

vector<int> varsXF, varsYF; // Maps X_i/Y_i -> Id in FAig
vector<int> Xi2Ci_Skolem, Yi2Co_Skolem; // Maps X_i/Y_i -> Ci/Co num in SkolemAig
vector<int> Ci2Xi_Skolem;
vector<int> Yi2Ci_Skolem; // Maps Y_i -> Ci num in SkolemAig (After FAig Transfer)
int numOrigInputs, numX, numY;
Abc_Frame_t* pAbc;

map<string,int> name2IdF;
map<int,string> id2NameF;
map<string,int> name2CiSkolem;
map<int,string> Ci2NameSkolem;
map<string,int> name2CoSkolem;
map<int,string> Co2NameSkolem;

void printNtkAig(Abc_Ntk_t* pNtk, Aig_Man_t* pAig);
Abc_Ntk_t* getNtk(string pFileName);
void populateVars(Abc_Ntk_t* FNtk, Abc_Ntk_t* skolemNtk, string varsFile);
string getFileName(string s);


chrono_steady_time helper_time_measure_start = TIME_NOW;
chrono_steady_time main_time_start = TIME_NOW;

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

	Abc_Ntk_t * SNtk = Abc_NtkFromAigPhase(SAig);
	Abc_FrameSetCurrentNetwork(pAbc, SNtk);

	command = "rewrite -lz; refactor -l;";

	TIME_MEASURE_START
	cout << "balancing... ";
	if (Cmd_CommandExecute(pAbc, "balance;")) {
		cout << "Cannot preprocess SNtk" << endl;
		return NULL;
	}
	cout << "took " << TIME_MEASURE_ELAPSED << endl;

	for (int i = 0; i < times; ++i)	{
		cout << "cycle " << i << ": " << command;
		TIME_MEASURE_START
		if (Cmd_CommandExecute(pAbc, (char*)command.c_str())) {
			cout << "Cannot preprocess SNtk, took " << TIME_MEASURE_ELAPSED << endl;
			return NULL;
		}
		cout << "took " << TIME_MEASURE_ELAPSED << endl;
	}

	TIME_MEASURE_START
	cout << "balancing... ";
	if (Cmd_CommandExecute(pAbc, "balance;")) {
		cout << "Cannot preprocess SNtk" << endl;
		return NULL;
	}
	cout << "took " << TIME_MEASURE_ELAPSED << endl;

	SNtk = Abc_FrameReadNtk(pAbc);
	temp = Abc_NtkToDar(SNtk, 0, 0);
	Aig_ManStop(SAig);
	return temp;
}

int main(int argc, char const *argv[])
{
	if(argc!=3 and argc!=4) {
		cerr << "Incorrect Arguments. Run as ./verify benchmark.v skolemFile [vasFile = benchmark_varstoelim.txt]";
	}
	string benchmarkFile(argv[1]);
	string skolemFile(argv[2]);
	string varsOrderFile;
	if(argc == 4)
		varsOrderFile = string(argv[3]);
	else
		varsOrderFile = benchmarkFile.substr(0,benchmarkFile.find_last_of('.')) + "_varstoelim.txt";

	// ************
	// Read AIGs
	// ************
	Abc_Ntk_t* FNtk = getNtk(benchmarkFile);
	Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);
	Abc_Ntk_t* skolemNtk = getNtk(skolemFile);
	Aig_Man_t* skolemAig = Abc_NtkToDar(skolemNtk, 0, 0);

	// // Print FNtk, skolemNtk
	// cout << "\nF: " << endl;
	// printNtkAig(FNtk, FAig);
	// cout << "\nskolem: " << endl;
	// printNtkAig(skolemNtk, skolemAig);

	populateVars(FNtk, skolemNtk, varsOrderFile);
	assert(Aig_ManCiNum(FAig) == numX+numY);
	assert(Aig_ManCoNum(FAig) == 1);
	assert(Aig_ManCiNum(skolemAig) == numX);
	assert(Aig_ManCoNum(skolemAig) == numY);

	// ************
	// Print maps
	// ************
	cout << "X (inputs):" << endl;
	for (int i = 0; i < numX; ++i) {
		printf("%d: ",i);
		printf("F(Id %d, Name %s): ", varsXF[i], id2NameF[varsXF[i]].c_str());
		printf("Skolem(Ci %d, Name %s)\n", Xi2Ci_Skolem[i], Ci2NameSkolem[Xi2Ci_Skolem[i]].c_str());
	}
	cout << endl;
	cout << "Y (outputs):" << endl;
	for (int i = 0; i < numY; ++i) {
		printf("%d: ",i);
		printf("F(Id %d, Name %s): ", varsYF[i], id2NameF[varsYF[i]].c_str());
		printf("Skolem(Co %d, Name %s)\n", Yi2Co_Skolem[i], Co2NameSkolem[Yi2Co_Skolem[i]].c_str());
	}
	cout << endl;

	// ************
	// Permute FAig inputs to match skolemAig
	// ************
	Vec_Ptr_t * vPis = Vec_PtrAlloc(numX + numY);
	Vec_Ptr_t * vPos = Vec_PtrAlloc(1);
	for (int i = 0; i < numX; ++i) {
		Vec_PtrPush(vPis, Aig_ManObj(FAig, varsXF[Ci2Xi_Skolem[i]]));
	}
	Yi2Ci_Skolem.resize(numY);				// Book-keeping
	for (int i = 0; i < numY; ++i) {
		Vec_PtrPush(vPis, Aig_ManObj(FAig, varsYF[i]));
		Yi2Ci_Skolem[i] = numX+i; 			// Book-keeping
	}
	Vec_PtrPush(vPos, Aig_ManCo(FAig,0));
	Aig_Man_t* FAig_ordered = Aig_ManDupSimpleDfsPart(FAig, vPis, vPos);

	// cout << "FAig_ordered" << endl;
	// printAig(FAig_ordered);

	// ************
	// Transfer FAig_ordered to skolemAig
	// ************
	cout << "Transfer FAig to skolemAig..." << endl;
	Aig_Obj_t* F = Aig_Transfer(FAig_ordered, skolemAig, Aig_ObjChild0(Aig_ManCo(FAig_ordered,0)), numOrigInputs);
	Aig_ObjCreateCo(skolemAig, F);
	int FCoNum = Aig_ManCoNum(skolemAig)-1;

	// cout << "skolemAig after transfer" << endl;
	// printAig(skolemAig);

	// Compress!
	Aig_ManPrintStats( skolemAig );
	cout << "Compressing skolemAig..." << endl;
	skolemAig = compressAigByNtkMultiple(skolemAig, 3);
	assert(skolemAig != NULL);
	Aig_ManPrintStats( skolemAig );

	// ************
	// Start Verification
	// ************
	Aig_ObjCreateCo(skolemAig, Aig_ObjChild0(Aig_ManCo(skolemAig, FCoNum)));
	int FPrimeCoNum = Aig_ManCoNum(skolemAig)-1;

	// Substitute
	cout << "Substituting..." << endl;
	Aig_Obj_t* F_subs = Aig_ObjChild0(Aig_ManCo(skolemAig, FCoNum));
	for (int i = 0; i < numY; ++i) {
		TIME_MEASURE_START
		Aig_Obj_t* skolemFunc = Aig_ObjChild0(Aig_ManCo(skolemAig, Yi2Co_Skolem[i]));
		int CiNum = Yi2Ci_Skolem[i];
		F_subs = Aig_Compose(skolemAig, F_subs, skolemFunc, CiNum);
		printf("Done %d/%d, took %f; ", i, numY, TIME_MEASURE_ELAPSED);
		Aig_ManPrintStats( skolemAig );
	}

	Aig_ObjPatchFanin0(skolemAig, Aig_ManCo(skolemAig,FCoNum), F_subs);
	int FSubsCoNum = FCoNum;
	// Aig_ObjCreateCo(skolemAig, F_subs);
	// int FSubsCoNum = Aig_ManCoNum(skolemAig)-1;

	// Compress!
	Aig_ManPrintStats( skolemAig );
	cout << "Compressing skolemAig..." << endl;
	skolemAig = compressAigByNtkMultiple(skolemAig, 3);
	assert(skolemAig != NULL);
	Aig_ManPrintStats( skolemAig );

	// Aig_ManCleanup(skolemAig);
	// printAig(skolemAig);
	// cout << "FSubsCoNum: " << FSubsCoNum << endl;
	// cout << "FPrimeCoNum: " << FPrimeCoNum << endl;

	sat_solver* pSat = sat_solver_new();
	Cnf_Dat_t* skolemCnf = Cnf_Derive(skolemAig, Aig_ManCoNum(skolemAig));
	addCnfToSolver(pSat, skolemCnf);

	lit LA[3];
	LA[0] = toLitCond(getCnfCoVarNum(skolemCnf, skolemAig, FSubsCoNum),1);
	LA[1] = toLitCond(getCnfCoVarNum(skolemCnf, skolemAig, FPrimeCoNum),0);

	cout << "Calling SAT Solver..." << endl;
	int status = sat_solver_solve(pSat, LA, LA+2, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
	if (status == l_False) {
		cout << "Verified!" << endl;
	}
	else if (status == l_True) {
		cout << "Not Verified!" << endl;
		cerr << "Not Verified!" << endl;
	}
	sat_solver_delete(pSat);
	Cnf_DataFree(skolemCnf);

	return 0;
}

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

int getCnfCoVarNum(Cnf_Dat_t* cnf, Aig_Man_t* aig, int nthCo) {
	return cnf->pVarNums[((Aig_Obj_t *)Vec_PtrEntry(aig->vCos, nthCo))->Id];
}

void printAig(Aig_Man_t* pMan) {
	int i;
	Aig_Obj_t* pAigObj;
	cout << "Aig: " << endl;
	Aig_ManForEachObj( pMan, pAigObj, i )
	    Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
	cout << endl;
}

void printNtkAig(Abc_Ntk_t* pNtk, Aig_Man_t* pAig) {
	int i;
	Abc_Obj_t* pAbcObj;
	Abc_NtkForEachObj(pNtk,pAbcObj,i)
		cout <<"Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;
	cout << endl;

	printAig(pAig);
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

Abc_Ntk_t*  getNtk(string pFileName) {
	pAbc = Abc_FrameGetGlobalFrame();
	string cmd = "read " + pFileName;
	if (CommandExecute(pAbc, cmd)) { // Read the AIG
		return NULL;
	}
	cmd = "balance";
	if (CommandExecute(pAbc, cmd)) { // Simplify
		return NULL;
	}
	Abc_Ntk_t* pNtk =  Abc_FrameReadNtk(pAbc);
	return Abc_NtkDup(pNtk);
}

void populateVars(Abc_Ntk_t* FNtk, Abc_Ntk_t* skolemNtk, string varsFile) {

	assert(varsXF.empty());
	assert(varsYF.empty());

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

	// Handling SkolemAig
	Abc_NtkForEachCi( skolemNtk, pPi, i ) {
		string variable_name = Abc_ObjName(pPi);
		name2CiSkolem[variable_name] = i;
		Ci2NameSkolem[i] = variable_name;
	}
	Abc_NtkForEachCo( skolemNtk, pPi, i ) {
		string variable_name = Abc_ObjName(pPi);
		name2CoSkolem[variable_name] = i;
		Co2NameSkolem[i] = variable_name;
	}

	// Combining Info for Xi2Ci_Skolem, Yi2Co_Skolem
	assert(Xi2Ci_Skolem.empty());
	assert(Yi2Co_Skolem.empty());

	for (int i = 0; i < numX; ++i) {
		string XiName = id2NameF[varsXF[i]];
		assert(name2CiSkolem.count(XiName) > 0);
		int CiSkolem = name2CiSkolem[XiName];
		Xi2Ci_Skolem.push_back(CiSkolem);
	}
	for (int i = 0; i < numY; ++i) {
		string YiName = id2NameF[varsYF[i]];
		assert(name2CoSkolem.count(YiName) > 0);
		int CoSkolem = name2CoSkolem[YiName];
		Yi2Co_Skolem.push_back(CoSkolem);
	}

	Ci2Xi_Skolem.resize(numX,-1);
	for (int i = 0; i < numX; ++i)
		Ci2Xi_Skolem[Xi2Ci_Skolem[i]] = i;
	vector<int>Co2Yi_Skolem(numY);
	for (int i = 0; i < numY; ++i)
		Co2Yi_Skolem[Yi2Co_Skolem[i]] = i;
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
