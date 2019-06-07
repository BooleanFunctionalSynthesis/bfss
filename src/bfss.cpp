
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
#include "helper.h"
#include "nnf.h"

using namespace std;

////////////////////////////////////////////////////////////////////////
///                           GLOBALS                                ///
////////////////////////////////////////////////////////////////////////
vector<int> varsSInv;
vector<int> varsXF, varsXS;
vector<int> varsYF, varsYS; // to be eliminated
int numOrigInputs = 0, numX = 0, numY = 0;
vector<string> varsNameX, varsNameY;
Abc_Frame_t* pAbc = NULL;
sat_solver* m_pSat = NULL;
Cnf_Dat_t* m_FCnf = NULL;
lit m_f = 0;
double sat_solving_time = 0;
double verify_sat_solving_time = 0;
double reverse_sub_time = 0;
chrono_steady_time helper_time_measure_start = TIME_NOW;
chrono_steady_time main_time_start = TIME_NOW;

////////////////////////////////////////////////////////////////////////
///                            MAIN                                  ///
////////////////////////////////////////////////////////////////////////
int main(int argc, char * argv[]) {
	Abc_Obj_t* pAbcObj;
	Aig_Obj_t* pAigObj;
	map<string, int> name2IdF;
	map<int, string> id2NameF;
	int i, j;
	vector<int> cex;

	parseOptions(argc, argv);

	main_time_start = TIME_NOW;
	auto main_end = TIME_NOW;
	double total_main_time;

	OUT("get FNtk..." );
	Abc_Ntk_t* FNtk = getNtk(options.benchmark,true);
	OUT("get FAig..." );
	Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);

	int removed_first = Aig_ManCleanup(FAig);
	cout << "Removed " << removed_first << " in the first cleanup" << endl;

	vector<int> unate;
	int numTotUnates = 0;
	if(!options.noUnate) {

		cout << "\n\nChecking Unates..." << endl;

		varsXF.clear();
		varsYF.clear();
		name2IdF.clear();
		id2NameF.clear();

		vector<string> varOrder;

		cout << "populateVars" << endl;
		populateVars(FNtk, options.varsOrder, varOrder,
						varsXF, varsYF,
						name2IdF, id2NameF);

		cout << "numX " << numX << endl;
		cout << "numY " << numY << endl;

		unate.resize(numY, -1);
		auto unate_start = TIME_NOW;

		// find unates, substitute
		int n, numSynUnates = 0;
		if(!options.noSyntacticUnate ) {
			while((n = checkUnateSyntacticAll(FAig, unate)) > 0) {
				substituteUnates(FAig, unate);
				numSynUnates += n;
			}
		}
		cout << "Syntactic Unates Done" << endl;
		int numSemUnates = 0;
		//int numSemUnates1 = 0;
		if(!options.noSemanticUnate ) {	//Semantic Unate checks on the remaining variables - SS
			numSemUnates = checkUnateSemAll (FAig, unate);
			//numSemUnates1 = checkUnateSemanticAll(FAig, unate1);
			//assert (numSemUnates == numSemUnates1);
			substituteUnates(FAig, unate);
		}

		numTotUnates = numSynUnates + numSemUnates;
		auto unate_end = TIME_NOW;
		auto unate_run_time = std::chrono::duration_cast<std::chrono::microseconds>(unate_end - unate_start).count()/1000000.0;
		cout << "Total Syntactic Unates: " << numSynUnates << endl;
		cout << "Total Semantic  Unates: " << numSemUnates << endl;
		cout << "Total Unate Run-Time:   " << unate_run_time << endl;

		cout << "Unates: ";
		for (int i = 0; i < numY; ++i)
			cout << unate[i] << " ";
		cout << endl;

		// cleanup after unates
		varsXF.clear();
		varsYF.clear();
		name2IdF.clear();
		id2NameF.clear();
	}

	
	Nnf_Man nnfNew;
	if(options.useBDD) {
		// ************************
		// Creating BDD Start
		Abc_Ntk_t* FNtkSmall = Abc_NtkFromAigPhase(FAig);
		cout << "Creating BDD..." << endl;
		TIME_MEASURE_START
		// Abc_NtkBuildGlobalBdds(FNtkSmall, int fBddSizeMax, int fDropInternal, int fReorder, int fVerbose );
		DdManager* ddMan = (DdManager*)Abc_NtkBuildGlobalBdds(FNtkSmall, 1e10, 1, 1, 1);
		auto bdd_end = TIME_NOW;
		cout << "Created BDD!" << endl;
		DdNode* FddNode = (DdNode*)Abc_ObjGlobalBdd(Abc_NtkCo(FNtkSmall,0));
		cout << "Time taken:   " << TIME_MEASURE_ELAPSED << endl;
		cout << "BDD Size:     " << Cudd_DagSize(FddNode) << endl;
		assert(ddMan->size == Abc_NtkCiNum(FNtkSmall));
		// Creating BDD End
		// **************************
		
		nnfNew.init(ddMan, FddNode);
		cout << "Created NNF from BDD" << endl;
	}
	else {
		nnfNew.init(FAig);
		cout << "Created NNF from FAig" << endl;
	}

	// <<<<<<< HEAD
	// Nnf_Man nnfNew(FAig);

	// int numYforClouds = getNumY(options.varsOrder);
	// Aig_Man_t* SAig = nnfNew.createAigMultipleClouds(2*numYforClouds, CiCloudIth, CoIth);

	// cout << "\n\nMultiple Cloud Aig: " << endl;
	// printAig(SAig);

	// // Aig_Man_t* normalAig = nnfNew.createAigWithoutClouds();
	// // cout << "\n\nNormal Aig: " << endl;
	// // printAig(normalAig);


	// numOrigInputs = nnfNew.getCiNum();
	// =======


	// Aig_Man_t* cloudAig = nnfNew.createAigWithClouds();
	// cout << "\n\nCloud Aig: " << endl;
	// printAig(cloudAig);

	// Aig_Man_t* multiCloudAig = nnfNew.createAigMultipleClouds(4);
	// cout << "\n\nMultiple Cloud Aig: " << endl;
	// printAig(multiCloudAig);

	// Aig_Man_t* normalAig = nnfNew.createAigWithoutClouds();
	// cout << "\n\nNormal Aig: " << endl;
	// printAig(normalAig);

	numOrigInputs = nnfNew.getCiNum();
	Aig_Man_t* SAig = nnfNew.createAigWithoutClouds();

	OUT("Aig_ManCoNum(SAig): " << Aig_ManCoNum(SAig));
	populateVars(FNtk, nnfNew, options.varsOrder,
					varsXF, varsXS,
					varsYF, varsYS,
					name2IdF, id2NameF);

	if(options.noUnate) unate.resize(numY, -1);

	cout << "numX " << numX << endl;
	cout << "numY " << numY << endl;
	cout << "numUnate " << numY - count(unate.begin(), unate.end(), -1) << endl;
	cout << "numOrigInputs " << numOrigInputs << endl;

	#ifdef DEBUG_CHUNK // Print varsXS, varsYS
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

	// Populate Input Name Vectors (Same for SAig and FAig)
	assert(varsNameX.empty());
	assert(varsNameY.empty());
	for(auto id:varsXF)
		varsNameX.push_back(id2NameF[id]);
	for(auto id:varsYF)
		varsNameY.push_back(id2NameF[id]);

	OUT("Cleaning up...");
	int removed = Aig_ManCleanup(SAig);
	OUT("Removed "<<removed<<" nodes");

	bool isWDNNF = (numTotUnates == numY); //false;
	if(options.checkWDNNF && (! isWDNNF)) {
		// populate varsYNNF: vector of input numbers
		vector<int> varsYNNF;
		for(auto y:varsYF) {
			int i;
			for (i = 0; i < nnfNew.getCiNum(); ++i)
				if(nnfNew.getCiPos(i)->OrigAigId == y)
					break;
			assert(i != nnfNew.getCiNum());
			varsYNNF.push_back(i);
		}

		cout << "Checking wDNNF" << endl;
		isWDNNF = nnfNew.isWDNNF(varsYNNF);
	}
	if(isWDNNF) {
		cout << "********************************" << endl;
		cout << "** In wDNNF!" << endl;
		cout << "** Will Predict Exact Skolem Fns" << endl;
		cout << "********************************" << endl;
	}
	else {
		cout << "********************************" << endl;
		cout << "** Not wDNNF :(" << endl;
		cout << "********************************" << endl;
	}

	Aig_ManPrintStats( SAig );
	cout << "Compressing SAig..." << endl;
	SAig = compressAigByNtkMultiple(SAig, 3);
	assert(SAig != NULL);
	Aig_ManPrintStats( SAig );

	// Fs[0] - F_SAig      will always be Aig_ManCo( ... , 1)
	// Fs[1] - FPrime_SAig will always be Aig_ManCo( ... , 2)
	vector<Aig_Obj_t* > Fs(2);
	vector<vector<int> > r0(numY), r1(numY);
	cout << "initializeCompose(SAig, Fs, r0, r1)..."<<endl;
	clock_t compose_start = clock();
	initializeCompose(SAig, Fs, r0, r1, unate);
	clock_t compose_end = clock();
	cout<< "Mega compose time: " <<double(compose_end-compose_start)/CLOCKS_PER_SEC << endl;

	Aig_Obj_t* F_SAig = Fs[0];
	Aig_Obj_t* FPrime_SAig = Fs[1];
	Aig_ManSetCioIds(SAig);
	F_SAigIndex = F_SAig->CioId;
	FPrime_SAigIndex = FPrime_SAig->CioId;
	cout << "F_SAigIndex: " << F_SAigIndex << endl;
	cout << "FPrime_SAigIndex: " << FPrime_SAigIndex << endl;

	if(options.monoSkolem) {
		monoSkolem(SAig, r0, r1);
		main_end = TIME_NOW;
		total_main_time = std::chrono::duration_cast<std::chrono::microseconds>(main_end - main_time_start).count()/1000000.0;
		cout << "Found Skolem Functions" << endl;
		cout<< "Total main time: (monoskolem)   " << total_main_time << endl;
		chooseR_(SAig,r0,r1);
		verifyResult(SAig, r0, r1, 0);
		cout<< "Verify SAT solving time: " << verify_sat_solving_time << endl;
		return 1;
	}

	// Patch 0th Output of SAig (is taking un-necessary size)
	Aig_ObjPatchFanin0(SAig, Aig_ManCo(SAig,0), Aig_ManConst0(SAig));

	// Global Optimization: Used in dinfing k2Max
	if(!isWDNNF) {
		m_pSat = sat_solver_new();
		m_FCnf = Cnf_Derive(SAig, Aig_ManCoNum(SAig));
		m_f = toLitCond(getCnfCoVarNum(m_FCnf, SAig, F_SAigIndex), 0);
		addCnfToSolver(m_pSat, m_FCnf);
	}

	#ifdef DEBUG_CHUNK // Print SAig, checkSupportSanity
		cout << "\nSAig: " << endl;
		Abc_NtkForEachObj(SNtk,pAbcObj,i)
			cout <<"SAig Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

		cout << "\nSAig: " << endl;
		Aig_ManForEachObj( SAig, pAigObj, i )
			Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );

		cout << "checkSupportSanity(SAig, r0, r1)..."<<endl;
		checkSupportSanity(SAig, r0, r1);
	#endif
	cout << "Created SAig..." << endl;
	cout << endl;

	options.c1 = (options.c1 >= numY)? numY - 1 : options.c1;
	options.c2 = (options.c2 >= numY)? numY - 1 : options.c2;

	// Pre-process R0/R1
	k2Trend = vector<vector<int> >(numY+1, vector<int>(numY,0));
	useR1AsSkolem = vector<bool>(numY,true);

	initializeAddR1R0toR();
	if(options.proactiveProp)
		switch(options.skolemType) {
			case (sType::skolemR0): propagateR0Cofactors(SAig,r0,r1); break;
			case (sType::skolemR1): propagateR1Cofactors(SAig,r0,r1); break;
			case (sType::skolemRx): propagateR0R1Cofactors(SAig,r0,r1); break;
		}
	chooseR_(SAig,r0,r1);
	cout << endl;

	Aig_ManPrintStats( SAig );
	cout << "Compressing SAig..." << endl;
	SAig = compressAigByNtkMultiple(SAig, 2);
	assert(SAig != NULL);
	Aig_ManPrintStats( SAig );
	#ifdef DEBUG_CHUNK // Print SAig, checkSupportSanity
		cout << "\nSAig: " << endl;
		Aig_ManForEachObj( SAig, pAigObj, i )
			Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );

		cout << "checkSupportSanity(SAig, r0, r1)..."<<endl;
		checkSupportSanity(SAig, r0, r1);
	#endif

	// cex = vector<int>(2*numOrigInputs, 0);
	int M = -1;
	int k1Level = -1;
	int k1MaxLevel = -1;
	int numloops = 0;

	if(isWDNNF) {
		cout << "In WDNNF, Skipping CEGAR Loop..."<<endl;
	}
	else {
		// CEGAR Loop
		cout << "Starting CEGAR Loop..."<<endl;
		// while(callSATfindCEX(SAig, cex, r0, r1)) {
		while(getNextCEX(SAig, M, k1Level, k1MaxLevel, r0, r1)) {
			OUT("Iter " << numloops << ":\tFound CEX!");
			// cout<<'.'<<flush;
			// evaluateAig(SAig, cex);
			#ifdef DEBUG_CHUNK
				checkCexSanity(SAig, cex, r0, r1);
			#endif
			updateAbsRef(SAig, M, k1Level, k1MaxLevel, r0, r1);
			numloops++;

			if(numloops % 50 == 0) {
				cout << numloops;
				cout << endl;
				Aig_ManPrintStats( SAig );
				cout << "Compressing SAig..." << endl;
				SAig = compressAigByNtk(SAig);
				// SAig = compressAig(SAig);
				assert(SAig != NULL);
				Aig_ManPrintStats( SAig );
			}
		}
		cout<<endl;
	}


	#ifdef DEBUG_CHUNK // Print SAig
		cout << "\nSAig: " << endl;
		Aig_ManForEachObj( SAig, pAigObj, i )
			Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
	#endif

	// printK2Trend();

	cout << "Found Skolem Functions" << endl;
	cout << "Num Iterations: " << numloops << endl;
	cout << "Num Fixes:      " << numFixes << endl;
	cout << "Num CEX:        " << numCEX << endl;
	cout << "Num CEX Used:   " << numCEXUsed << endl;
	cout << "Total Size: ";
	Aig_ManPrintStats(SAig);
	cout << endl;


	main_end = TIME_NOW;
	total_main_time = std::chrono::duration_cast<std::chrono::microseconds>(main_end - main_time_start).count()/1000000.0;
	cout<< "Total main time:         " << total_main_time << endl;
	cout<< "Total SAT solving time:  " << sat_solving_time << endl;
	#ifndef NO_UNIGEN
	cout<< "Total Dead time:         " << CMSat::CUSP::totalDeadTime << endl;
	#else
	cout<< "Total Dead time:         " << 0 << endl;
	#endif

	verifyResult(SAig, r0, r1, 0);
	cout<< "Verify SAT solving time: " << verify_sat_solving_time << endl;

	if(m_pSat!=NULL) sat_solver_delete(m_pSat);
	if(m_FCnf!=NULL) Cnf_DataFree(m_FCnf);

	// Stop ABC
	Abc_Stop();
	return 0;
}
