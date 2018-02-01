
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
#include "helper.h"
// #include "formula.h"
#include "nnf.h"

using namespace std;

////////////////////////////////////////////////////////////////////////
///                           GLOBALS                                ///
////////////////////////////////////////////////////////////////////////
vector<int> varsSInv;
vector<int> varsXF, varsXS;
vector<int> varsYF, varsYS; // to be eliminated
int numOrigInputs, numX, numY;
Abc_Frame_t* pAbc;
sat_solver* m_pSat;
Cnf_Dat_t* m_FCnf;
lit m_f;
double sat_solving_time = 0;
double verify_sat_solving_time = 0;
double reverse_sub_time = 0;

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

	auto main_start = std::chrono::steady_clock::now();
	auto main_end = std::chrono::steady_clock::now();
	double total_main_time;

	OUT("get FNtk..." );
	Abc_Ntk_t* FNtk = getNtk(options.benchmark,true);
	OUT("get FAig..." );
	Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);
	int removed_first = Aig_ManCleanup(FAig);
	cout << "Removed " << removed_first << " in the first cleanup" << endl;


	vector<int> unate;
	if(!options.noUnate) {

		varsXF.clear();
		varsYF.clear();
		name2IdF.clear();
		id2NameF.clear();

		cout << "populateVars" << endl;
		populateVars(FNtk, options.varsOrder,
						varsXF, varsYF,
						name2IdF, id2NameF);

		cout << "numX " << numX << endl;
		cout << "numY " << numY << endl;

		unate.resize(numY, -1);
		// find unates, substitute
		cout << "checkUnateAll" << endl;
		auto unate_start = std::chrono::steady_clock::now();

		int numSynUnates = 0;
		int n;
		while((n = checkUnateSyntacticAll(FAig, unate)) > 0) {
			substituteUnates(FAig, unate);
			numSynUnates += n;
		}
		int numSemUnates = checkUnateSemanticAll(FAig, unate);
		substituteUnates(FAig, unate);

		auto unate_end = std::chrono::steady_clock::now();
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


	Nnf_Man nnfNew(FAig);

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

	cout << "numX " << numX << endl;
	cout << "numY " << numY << endl;
	cout << "numUnate " << numY - count(unate.begin(), unate.end(), -1) << endl;
	cout << "numOrigInputs " << numOrigInputs << endl;

	unate.resize(numY, -1);

	#ifdef DEBUG_CHUNK // Print varsXS, varsYS
		// cout << "varsXF: " << endl;
		// for(auto it : varsXF)
		//     cout << it << " ";
		// cout<<endl;
		// cout << "varsYF: " << endl;
		// for(auto it : varsYF)
		//     cout << it << " ";
		// cout<<endl;

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

	OUT("Cleaning up...");
	int removed = Aig_ManCleanup(SAig);
	OUT("Removed "<<removed<<" nodes");


	// // @TODO: ============ DELETE THIS ===========
	// exit(0);

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

	// Pre-process R0/R1
	k2Trend = vector<vector<int> >(numY+1, vector<int>(numY,0));
	useR1AsSkolem = vector<bool>(numY,true);

	if(options.monoSkolem) {
		monoSkolem(SAig, r0, r1);
		main_end = std::chrono::steady_clock::now();
		total_main_time = std::chrono::duration_cast<std::chrono::microseconds>(main_end - main_start).count()/1000000.0;
		cout << "Found Skolem Functions" << endl;
		cout<< "Total main time: (monoskolem)   " << total_main_time << endl;
		chooseR_(SAig,r0,r1);
		assert(verifyResult(SAig, r0, r1, 0));
		cout<< "Verify SAT solving time: " << verify_sat_solving_time << endl;
		return 1;
	}

	m_pSat = sat_solver_new();
	m_FCnf = Cnf_Derive(SAig, Aig_ManCoNum(SAig));
	m_f = toLitCond(getCnfCoVarNum(m_FCnf, SAig, F_SAigIndex), 0);
	addCnfToSolver(m_pSat, m_FCnf);

	// cout << "checkSupportSanity(SAig, r0, r1)..."<<endl;
	// checkSupportSanity(SAig, r0, r1);

	// Patch 0th Output of SAig to F
	Aig_ObjPatchFanin0(SAig, Aig_ManCo(SAig,0), Aig_ManConst0(SAig));

	// #ifdef DEBUG_CHUNK // Print SAig
 //        cout << "\nSAig: " << endl;
 //        Abc_NtkForEachObj(SNtk,pAbcObj,i)
 //            cout <<"SAig Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

 //        cout << "\nSAig: " << endl;
 //        Aig_ManForEachObj( SAig, pAigObj, i )
 //            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
 //    #endif
	cout << "Created SAig..." << endl;
	cout << endl;

	options.c1 = (options.c1 >= numY)? numY - 1 : options.c1;
	options.c2 = (options.c2 >= numY)? numY - 1 : options.c2;

	initializeAddR1R0toR();

	if(options.proactiveProp)
		switch(options.skolemType) {
			case (sType::skolemR0): propagateR0Cofactors(SAig,r0,r1); break;
			case (sType::skolemR1): propagateR1Cofactors(SAig,r0,r1); break;
			case (sType::skolemRx): propagateR0R1Cofactors(SAig,r0,r1); break;
		}
	chooseR_(SAig,r0,r1);
	cout << endl;

	// cout << "checkSupportSanity(SAig, r0, r1)..."<<endl;
	// checkSupportSanity(SAig, r0, r1);

	Aig_ManPrintStats( SAig );
	cout << "Compressing SAig..." << endl;
	SAig = compressAigByNtk(SAig);
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

	// CEGAR Loop
	cout << "Starting CEGAR Loop..."<<endl;
	int numloops = 0;
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


	main_end = std::chrono::steady_clock::now();
	total_main_time = std::chrono::duration_cast<std::chrono::microseconds>(main_end - main_start).count()/1000000.0;
	cout<< "Total main time:         " << total_main_time << endl;
	cout<< "Total SAT solving time:  " << sat_solving_time << endl;
	cout<< "Total Dead time:         " << CMSat::CUSP::totalDeadTime << endl;

	assert(verifyResult(SAig, r0, r1, 0));
	cout<< "Verify SAT solving time: " << verify_sat_solving_time << endl;

	sat_solver_delete(m_pSat);
	Cnf_DataFree(m_FCnf);

	// Stop ABC
	Abc_Stop();
	return 0;
}
