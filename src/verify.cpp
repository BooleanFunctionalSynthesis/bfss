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

vector<vector<int> > allClauses;
int numVars, numClauses;
vector<int> varsXFCopy;
set<int> varsYFCopy;
vector<int>missingIds;

void printNtkAig(Abc_Ntk_t* pNtk, Aig_Man_t* pAig);
Abc_Ntk_t* getNtk(string pFileName);
// void populateVars(Abc_Ntk_t* FNtk, Abc_Ntk_t* skolemNtk, string varsFile);
void populateVars(Abc_Ntk_t* FNtk, Aig_Man_t* FAig, Abc_Ntk_t* skolemNtk, string varsFile, bool verilogInput);
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

//Generate clauses for a = b and feed to the sat solver

/*
This gives an assert fail error on a few benchmarks 
void EquateCC (sat_solver * pSat, int a, int b )
{
    //cout << " Equating " << a << " and " << b << endl;
    lit Lits[2];
	Lits[0] = toLitCond( a, 0 );
	Lits[1] = toLitCond( b, 1 );
		cout << " Adding clause " <<  Lits [0] << " " << Lits [1] << endl;
    if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
         		assert( 0 );

	Lits[0] = toLitCond( a, 1 );
	Lits[1] = toLitCond( b, 0 );
	//	cout << " Adding clause " <<  Lits [0] << " " << Lits [1] << endl;
        	if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            		assert( 0 );
}
*/

//Copied  Equate in helper.cpp
bool EquateC(sat_solver *pSat, int varA, int varB) {
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

// temporarily copying this:
Aig_Man_t* QdimacsToAig(const char * qdFileName,  int& numVars, int& numClauses, vector<vector<int> >& allClauses) {
    char C[100], c;
    int tmpVar;
    Aig_Man_t* pMan = Aig_ManStart(0);

	FILE *qdFPtr = fopen (qdFileName, "r");

	// Number of variables and clauses
	fscanf (qdFPtr, "%c", &c);
	fscanf (qdFPtr, "%s", C);
	while (strcmp (C, "cnf") != 0)
		fscanf (qdFPtr, "%s", C);
	fscanf(qdFPtr, "%d %d", &numVars, &numClauses); // read first line p cnf
	cout << "numVars:       " <<  numVars << endl;
	cout << "NumClauses:   " << numClauses << endl;

	missingIds.resize(numVars+1, -1);
	int mIndex = 0;
	// Vars X
	
	fscanf (qdFPtr, "%c", &c);
	while (c != 'a')
		fscanf (qdFPtr, "%c", &c);
	fscanf(qdFPtr, "%d", &tmpVar);
	while (tmpVar !=0) {
		missingIds[tmpVar] = 1;
		varsXFCopy.push_back(tmpVar);
		fscanf(qdFPtr, "%d", &tmpVar);
	}
	cout << "varsXF.size(): " << varsXFCopy.size() << endl;
	assert (numVars > varsXFCopy.size());

	// Vars Y (to elim)
	fscanf (qdFPtr, "%c", &c);
	while (c != 'e')
	{
		fscanf (qdFPtr, "%c", &c);
	}
	cout << endl;
	fscanf(qdFPtr, "%d", &tmpVar);
	while (tmpVar !=0) {
		missingIds[tmpVar] = 1;
		varsYFCopy.insert(tmpVar);
		fscanf(qdFPtr, "%d", &tmpVar);
	}
	cout << "varsYF.size(): " << varsYFCopy.size() << endl;
	assert (numVars > varsYFCopy.size());
//The qdimacs file can have missing variables. This means that #a + #e < numVar
//Each such missing variable is considered as an input variable
	for (int i = 1; i <= numVars; i++)
		if (missingIds[i] == -1)
			varsXFCopy.push_back(i);
	// Update numVars = maxVar
	int maxVar = 0;
	for(auto it:varsXFCopy)
		maxVar = max(maxVar,it);
	for(auto it:varsYFCopy)
		maxVar = max(maxVar,it);
	cout << "maxVar:       " << maxVar << endl;
	if(maxVar < numVars) {
		 cout << "Setting numVars = " << maxVar << endl;
		 numVars = maxVar;
	}

	for (int i = 1; i <= numVars; i++) {
		Aig_Obj_t* ci = Aig_ObjCreateCi(pMan);
	//	cout << "created Ci " << i << endl;
	}

	// Clauses
	Aig_Obj_t* and_node;
	bool firstTwoCl = true;
	Aig_Obj_t* cl1 = NULL, *cl2 = NULL;
	for (int i = 0; i < numClauses ; i++) {
		vector<int> tempClause;
		fscanf(qdFPtr, "%d", &tmpVar);
		Aig_Obj_t* or_node;
		Aig_Obj_t* c1 = NULL, *c2 = NULL;
		bool first = true;
		while (tmpVar != 0) {
			tempClause.push_back(tmpVar);
			bool pos;
			if(tmpVar > 0) { // pos
				pos = true;
			}	
			else { // neg
				pos = false;
			}

			if (first) {
				if (c1 == NULL) {
					if (pos)
						c1 = Aig_ManCi(pMan, abs(tmpVar)-1);
					else
						c1 = Aig_Not(Aig_ManCi(pMan, abs(tmpVar)-1));
				}
				else if (c2 == NULL) {
					if (pos)
						c2 = Aig_ManCi(pMan, abs(tmpVar)-1);
					else
						c2 = Aig_Not(Aig_ManCi(pMan, abs(tmpVar)-1));
				}
				
				if (c1 != NULL && c2 != NULL) {
					or_node = Aig_Or(pMan, c1, c2);
					first = false;
				}
			}
			else {
				Aig_Obj_t* c = Aig_ManCi(pMan, abs(tmpVar)-1);
				if (!pos)
					c = Aig_Not(c);

				Aig_Obj_t* new_or_node = Aig_Or(pMan, or_node, c);
				or_node = new_or_node;
			}
			fscanf(qdFPtr, "%d", &tmpVar);
		}
		if (first && c1 != NULL && c2 == NULL) {
			or_node = Aig_Or(pMan, c1, Aig_ManConst0(pMan));
		}

		if(!tempClause.empty()) {
			allClauses.push_back(tempClause);
		}

		if (firstTwoCl) {
			if (cl1 == NULL)
				cl1 = or_node;
			else if (cl2 == NULL)
				cl2 = or_node;

			if (cl1 != NULL && cl2 != NULL) {
				and_node = Aig_And(pMan, cl1, cl2);
				firstTwoCl = false;
			}
		}
		else {
			Aig_Obj_t* new_and_node = Aig_And(pMan, and_node, or_node);
			and_node = new_and_node;
		}

		// if(tempClause.size() == 2) { // populate ___Implies
		// 	processBinaryClause(allClauses.size()-1);
		// }
	}
	if (firstTwoCl && cl1 != NULL && cl2 == NULL) {
		and_node = Aig_And(pMan, cl1, Aig_ManConst1(pMan));
	}

	Aig_ObjCreateCo(pMan, and_node);

	return pMan;

	fclose (qdFPtr);
}

int main(int argc, char const *argv[])
{
	// parseOptions(argc, (char**)argv);

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

	string fileName = benchmarkFile;
	string baseFileName = fileName.substr(fileName.find_last_of("/") + 1);  //Get the file name;
	cout << "BaseName:     " << baseFileName << endl;

	Aig_Man_t* FAig;
	Abc_Ntk_t* FNtk = NULL;
	bool verilogInput;
//	Abc_Obj_t *pObj;
	int i = 0;

	if (baseFileName.find("qdimacs") != string::npos) {
		OUT("read qdimacs file");
		OUT("get FAig..." );
		const char* inputfilename = benchmarkFile.c_str();
		FAig = QdimacsToAig(inputfilename,  numVars, numClauses, allClauses);
		cout << " Built FAig " << endl;
		verilogInput = false;
	}
	else {
//	else if ((baseFileName.substr(baseFileName.find_last_of(".") + 1) == "v" ) 
//|| 	(baseFileName.substr(baseFileName.find_last_of(".") + 1) ==  "aig" )) {
		cout  << "read verilog file";
		cout << "get FNtk..."  << benchmarkFile;
		FNtk = getNtk(benchmarkFile);
		FAig = Abc_NtkToDar(FNtk, 0, 0);
		verilogInput = true;
	}
	// ************
	// Read AIGs
	// ************
	// Abc_Ntk_t* FNtk = getNtk(benchmarkFile);
	// Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);
	Abc_Ntk_t* skolemNtk = getNtk(skolemFile);
	if (!verilogInput)
	{
    //Build a PI for each missing ID
		for (int i = 1; i <= numVars; i++)
		{
			if (missingIds[i] == -1)
			{
				Abc_Obj_t *p = Abc_NtkCreatePi(skolemNtk);
				Abc_ObjAssignName (p, (char *) to_string(i).c_str(), NULL);
			}
		}
	}

	Aig_Man_t* skolemAig = Abc_NtkToDar(skolemNtk, 0, 0);
	populateVars(FNtk, FAig, skolemNtk, varsOrderFile, verilogInput);
	assert(Aig_ManCiNum(FAig) >= numX+numY); 
	assert(Aig_ManCoNum(FAig) == 1);
	assert(Aig_ManCiNum(skolemAig) <= numX);
	assert((Aig_ManCoNum(skolemAig) >= numY) ); //Cadet generated skolem functions file has an extra output which denotes the value of the result.

	// ************
	// Print maps
	// ************
	cout << "X (inputs):" << endl;
	for (int i = 0; i < numX; ++i) {
		cout << i << ":";
		cout << "F(Id " << varsXF[i] << ", Name "  << id2NameF[varsXF[i]].c_str() << " ): "  ;
		cout << "Skolem(Ci " << Xi2Ci_Skolem[i] << " Name " <<  Ci2NameSkolem[Xi2Ci_Skolem[i]].c_str() << ");" << endl ;
	}
	cout << endl;
	cout << "Y (outputs):" << endl;
	for (int i = 0; i < numY; ++i) {
		cout << i << ":" << endl;
		cout << "F(Id " << varsYF[i] << ", Name "  << id2NameF[varsYF[i]].c_str() << " ): " << endl ;
		cout << "Skolem(Ci " << Yi2Co_Skolem[i] << " Name " <<  Co2NameSkolem[Yi2Co_Skolem[i]].c_str() << ");" <<   endl ;
		cout << "Co id " <<  Aig_ObjId(Aig_ManCo(skolemAig, Yi2Co_Skolem[i])) << endl;
	}
//Create Cnfs
	sat_solver* pSat = sat_solver_new();
	Cnf_Dat_t* skolemCnf = Cnf_Derive(skolemAig, Aig_ManCoNum(skolemAig));
    Cnf_Dat_t* FCnf = Cnf_Derive (FAig, Aig_ManCoNum(FAig));
	Cnf_Dat_t* FCnf_copy = Cnf_DataDup(FCnf);
    Cnf_DataLift (FCnf, FCnf_copy->nVars);
    Cnf_DataLift (skolemCnf, FCnf->nVars);
	addCnfToSolver(pSat, FCnf_copy);
	addCnfToSolver(pSat, FCnf);
	addCnfToSolver(pSat, skolemCnf);
   
 //  cout << "FCnf_copy->nVars " << FCnf_copy->nVars  << " FCnf->nVars " << FCnf->nVars << "skolemCnf->nVars " << skolemCnf->nVars << endl;
    
	cout << "Equating X (inputs):" << endl;
	for (int i = 0; i < numX; ++i) {
    //Equate //FCnf.X and FCnf_Copy.X
        EquateC (pSat,   FCnf->pVarNums[varsXF[i]], FCnf_copy -> pVarNums [varsXF[i]]);
    //Equate (FCnf.X and SkolemCI.X
        EquateC(pSat, FCnf->pVarNums[varsXF[i]], skolemCnf->pVarNums[Xi2Ci_Skolem[i]]); 

//	cout << "F(Id " << varsXF[i] << ", Name "  << id2NameF[varsXF[i]].c_str() << " ): "  ;
//		cout << "Skolem(Ci " << Xi2Ci_Skolem[i] << " Name " <<  Ci2NameSkolem[Xi2Ci_Skolem[i]].c_str() << ");" << endl ;
 //       cout << "Equating " << FCnf->pVarNums[varsXF[i]] << " and "  << skolemCnf->pVarNums[Xi2Ci_Skolem[i]]; 
  //      cout <<  "FCnf->pVarNums[varsXF[i]]" <<  " and " << FCnf_copy -> pVarNums [varsXF[i]] << endl;
	}
	cout << "Equating Y (outputs):" << endl;
	for (int i = 0; i < numY; ++i) {
       //SkolemCo and FCnf.Y 
//		cout << i << ":" << endl;
//		cout << "F(Id " << varsYF[i] << ", Name "  << id2NameF[varsYF[i]].c_str() << " ): " << endl ;
//		cout << "Skolem(Ci " << Yi2Co_Skolem[i] << " Name " <<  Co2NameSkolem[Yi2Co_Skolem[i]].c_str() << ");" <<   endl ;
//		cout << "Co id " <<  Aig_ObjId(Aig_ManCo(skolemAig, Yi2Co_Skolem[i])) << endl;
        EquateC(pSat, FCnf->pVarNums[varsYF[i]], skolemCnf->pVarNums[Aig_ObjId(Aig_ManCo(skolemAig, Yi2Co_Skolem[i]))]); 
 //       cout << "Equating " << FCnf->pVarNums[varsYF[i]] << " and " << skolemCnf->pVarNums[Aig_ObjId(Aig_ManCo(skolemAig, Yi2Co_Skolem[i]))] << endl; 
	}

    lit LA[2];
	LA[0] = toLitCond(FCnf->pVarNums[Aig_ManCo(FAig, 0)->Id], 1);
	LA[0] = toLitCond(FCnf_copy->pVarNums[Aig_ManCo(FAig, 0)->Id], 0);
//	LA[1] = toLitCond(getCnfCoVarNum(skolemCnf, skolemAig, FPrimeCoNum),0);

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

void populateVars(Abc_Ntk_t* FNtk, Aig_Man_t* FAig, Abc_Ntk_t* skolemNtk, string varsFile, bool verilogInput) {

	assert(varsXF.empty());
	assert(varsYF.empty());

	int i;
	Abc_Obj_t* pPi, *pObj;
	string line;
	if (!verilogInput) {
		FNtk = Abc_NtkFromAigPhase(FAig);

		//renameCi's
		Nm_ManFree(FNtk->pManName);
		FNtk->pManName = Nm_ManCreate(200);

		Abc_NtkForEachCi(FNtk, pObj, i) {
			Abc_ObjAssignName(pObj, (char*)to_string(pObj->Id).c_str(), NULL);
		}
	}

//check whether the name in FNtk and SkolemAig are the same in factorization and arithmetic benchmarks - TODO -SS

	Abc_NtkForEachCi( FNtk, pPi, i ) {
		 string variable_name = Abc_ObjName(pPi);
		 name2IdF[variable_name] = pPi->Id;
	}

	for(auto it:name2IdF)
		id2NameF[it.second] = it.first;

	if (verilogInput) {
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
	}
	else {
		for (auto it : name2IdF) {
			if (varsYFCopy.count(it.second) != 0)
				varsYF.push_back(it.second);
			else
				varsXF.push_back(it.second);
		}
		
	}

	numX = varsXF.size();
	numY = varsYF.size();
	numOrigInputs = numX + numY;

	//cout << " num X " <<  numX << " num Y" << numY << "numXCopy "  << varsXFCopy.size() << " " << varsYFCopy.size() << endl;

	if(numY <= 0) {
		cout << "Var File " + varsFile + " is empty!" << endl;
		cerr << "Var File " + varsFile + " is empty!" << endl;
		assert(numY > 0);
	}

	// Handling SkolemAig
	Abc_NtkForEachCi( skolemNtk, pPi, i ) {
		string variable_name = Abc_ObjName(pPi);
		//cout << "skolem var name " << variable_name << endl;
		name2CiSkolem[variable_name] = i;
		Ci2NameSkolem[i] = variable_name;
	}

	Abc_NtkForEachCo( skolemNtk, pPi, i ) {
		string variable_name = Abc_ObjName(pPi);
		name2CoSkolem[variable_name] = i;
		Co2NameSkolem[i] = variable_name;
	}

//	cout << "Ci2NameSkolem " <<  Ci2NameSkolem.size() << " " <<  numX;
//	cout << "Co2NameSkolem " << Co2NameSkolem.size() << " " <<  numY;
	// Combining Info for Xi2Ci_Skolem, Yi2Co_Skolem
	assert(Xi2Ci_Skolem.empty());
	assert(Yi2Co_Skolem.empty());

	for (int i = 0; i < numX; ++i) {
			string XiName = id2NameF[varsXF[i]];
				//cout << "XiName " << XiName << endl;
			assert (name2CiSkolem.count(XiName) > 0);
			int CiSkolem = name2CiSkolem[XiName];
				//cout << "CiSkolem for X  " << i << " is " << CiSkolem << endl;
			Xi2Ci_Skolem.push_back(CiSkolem);
	}	
	for (int i = 0; i < numY; ++i) {
				string YiName = id2NameF[varsYF[i]];
				assert( name2CoSkolem.count(YiName) > 0);
				int CoSkolem = name2CoSkolem[YiName];
				Yi2Co_Skolem.push_back(CoSkolem);
			}

	Ci2Xi_Skolem.resize(numX,-1);
	for (int i = 0; i < numX; ++i)
			Ci2Xi_Skolem[Xi2Ci_Skolem[i]] = i;
	vector<int>Co2Yi_Skolem(numY);
	for (int i = 0; i < numY; ++i)
			Co2Yi_Skolem[Yi2Co_Skolem[i]] = i;
//Need to fill the missing values?? SS
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


