
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
#include "helper.h"
#include "formula.h"

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

////////////////////////////////////////////////////////////////////////
///                            MAIN                                  ///
////////////////////////////////////////////////////////////////////////
int main(int argc, char * argv[]) {
	string pFileName, varsFile, benchmarkName;
	Abc_Obj_t* pAbcObj;
	Aig_Obj_t* pAigObj;
	map<string, int> name2IdF;
	map<int, string> id2NameF;
	int i, j;
	vector<int> cex;

	assert(argc == 2);
	benchmarkName = string(argv[1]);
	pFileName     = benchmarkName;
	varsFile      = benchmarkName.substr(0,benchmarkName.find_last_of('.')) +
					((argc==2)?"_varstoelim.txt":string(argv[2]));

	clock_t main_start = clock();

	OUT("get FNtk..." );
	Abc_Ntk_t* FNtk = getNtk(pFileName,true);
	OUT("get FAig..." );
	Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);

	AigToNNF nnf(FAig);
	OUT("parse..." );
	nnf.parse();
	numOrigInputs = nnf.getNumInputs();
	OUT("process..." );
	nnf.process();
	OUT("createAig..." );
	nnf.createAig();
	OUT("getNtk..." );
	Abc_Ntk_t* SNtk = nnf.getNtk();
	Aig_Man_t* SAig = Abc_NtkToDar(SNtk, 0, 0);

	// #ifdef DEBUG_CHUNK // Print FAig, SAig
	//     // cout << "\nAig_ManPrintVerbose FAig: " << endl;
	//     // Aig_ManPrintVerbose(FAig,1);
	//     // cout << "\nAig_ManPrintVerbose SAig: " << endl;
	//     // Aig_ManPrintVerbose(SAig,1);
	//     cout << "\nFAig: " << endl;
	//     Abc_NtkForEachObj(FNtk,pAbcObj,i)
	//         cout <<"FAig Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

	//     cout << endl;
	//     Aig_ManForEachObj( FAig, pAigObj, i )
	//         Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );

	//     cout << "\nSAig: " << endl;
	//     Abc_NtkForEachObj(SNtk,pAbcObj,i)
	//         cout <<"SAig Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

	//     cout << endl;
	//     Aig_ManForEachObj( SAig, pAigObj, i )
	//         Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
	// #endif

	#ifdef COMPARE_SAIGS // Compare SAig1 to old SAig
		AigToNNF nnf2(pFileName);
		OUT("nnf2 parse..." );
		nnf2.parse();
		OUT("nnf2 process..." );
		nnf2.process();
		OUT("nnf2 resetCounters..." );
		nnf2.resetCounters();
		OUT("nnf2 createAig..." );
		nnf2.createAig();
		OUT("nnf2 getNtk..." );
		Abc_Ntk_t* SNtk2 = nnf2.getNtk();
		OUT("nnf2 get AIGs..." );
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

	OUT("Aig_ManCoNum(SAig): " << Aig_ManCoNum(SAig));
	populateVars(FNtk, nnf, varsFile,
					varsXF, varsXS,
					varsYF, varsYS,
					name2IdF, id2NameF);
	numX = varsXS.size();
	numY = varsYS.size();

	cout << "numX " << numX << endl;
	cout << "numY " << numY << endl;
	cout << "numOrigInputs " << numOrigInputs << endl;
	#ifdef DEBUG_CHUNK // Print nnf.inputs, varsXS, varsYS
		// cout << "varsXF: " << endl;
		// for(auto it : varsXF)
		//     cout << it << " ";
		// cout<<endl;
		// cout << "varsYF: " << endl;
		// for(auto it : varsYF)
		//     cout << it << " ";
		// cout<<endl;
		cout << "nnf.inputs: " << endl;
		for(auto it: nnf.inputs) {
			cout << it->var_num << " ";
		}
		cout << endl;

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



	// F_SAig      will always be Aig_ManCo( ... , 1)
	// FPrime_SAig will always be Aig_ManCo( ... , 2)
	cout << "buildF(SAig)..."<<endl;
	Aig_Obj_t* F_SAig = buildF(SAig);

	m_pSat = sat_solver_new();
	m_FCnf = Cnf_Derive(SAig, Aig_ManCoNum(SAig));
	m_f = toLitCond(getCnfCoVarNum(m_FCnf, SAig, 1), 0);
	addCnfToSolver(m_pSat, m_FCnf);

	cout << "buildFPrime(SAig)..."<<endl;
	Aig_Obj_t* FPrime_SAig = buildFPrime(SAig, F_SAig);
	vector<vector<int> > r0(numY), r1(numY);
	cout << "initializeRs(SAig, r0, r1)..."<<endl;
	initializeR0(SAig, r0);
	initializeR1(SAig, r1);

	// cout << "checkSupportSanity(SAig, r0, r1)..."<<endl;
	// checkSupportSanity(SAig, r0, r1);

	// Patch 0th Output of SAig to F
	pAigObj = Aig_ManCo(SAig,0);
	F_SAig  = Aig_ManCo(SAig,1);
	F_SAig  = Aig_ObjChild0(F_SAig);
	Aig_ObjPatchFanin0(SAig, pAigObj, F_SAig);

	// #ifdef DEBUG_CHUNK // Print SAig
 //        cout << "\nSAig: " << endl;
 //        Abc_NtkForEachObj(SNtk,pAbcObj,i)
 //            cout <<"SAig Node "<<i<<": " << Abc_ObjName(pAbcObj) << endl;

 //        cout << "\nSAig: " << endl;
 //        Aig_ManForEachObj( SAig, pAigObj, i )
 //            Aig_ObjPrintVerbose( pAigObj, 1 ), printf( "\n" );
 //    #endif
	cout << "Created SAig..." << endl;

	initializeAddR1R0toR();
	propagateR1Cofactors(SAig,r0,r1);
	cout << "checkSupportSanity(SAig, r0, r1)..."<<endl;
	checkSupportSanity(SAig, r0, r1);

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

	// CEGAR Loop
	cout << "Starting CEGAR Loop..."<<endl;
	int numloops = 0;
	// while(callSATfindCEX(SAig, cex, r0, r1)) {
	while(getNextCEX(SAig, M, r0, r1)) {
		OUT("Iter " << numloops << ":\tFound CEX!");
		// cout<<'.'<<flush;
		// evaluateAig(SAig, cex);
		#ifdef DEBUG_CHUNK
			checkCexSanity(SAig, cex, r0, r1);
		#endif
		updateAbsRef(SAig, r0, r1, M);
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



	cout << "Found Skolem Functions" << endl;
	cout << "Num Iterations: " << numloops << endl;

	assert(verifyResult(SAig, r0, r1, 0));

	clock_t main_end = clock();
	cout<< "Total time:   " <<double( main_end-main_start)/CLOCKS_PER_SEC << endl;

	sat_solver_delete(m_pSat);
	Cnf_DataFree(m_FCnf);

	// Stop ABC
	Abc_Stop();
	return 0;
}
