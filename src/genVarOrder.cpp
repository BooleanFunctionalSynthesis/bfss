
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
#include "helper.h"

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

vector<int> calculateLeastOccurence(Aig_Man_t* FAig) {
	Aig_Obj_t* pObj; int i;
	unordered_map<int, vector<bool> > nodeSupport;
	vector<bool> initVec(numY, false);
	vector<int>  ranks(numY,0);

	for (int i = 0; i < numX; ++i) {
		nodeSupport[varsXF[i]] = initVec;
	}
	for (int i = 0; i < numY; ++i) {
		vector<bool> updateVec(numY, false);
		updateVec[i] = true;
		nodeSupport[varsYF[i]] = updateVec;
	}
	Aig_ManForEachObj(FAig, pObj, i) {
		if(pObj->Id > numOrigInputs) {
			vector<bool> updateVec(numY, false), lVec(numY, false), rVec(numY, false);
			if(Aig_ObjFanin0(pObj) != NULL)
				lVec = nodeSupport[Aig_ObjFanin0(pObj)->Id];
			if(Aig_ObjFanin1(pObj) != NULL)
				rVec = nodeSupport[Aig_ObjFanin1(pObj)->Id];
			for(int i = 0; i < numY; ++i) {
				updateVec[i] = lVec[i] || rVec[i];
				if(updateVec[i]) {
					ranks[i]++;
				}
			}
			nodeSupport[pObj->Id] = updateVec;
		}
	}
	return ranks;
}

////////////////////////////////////////////////////////////////////////
///                            MAIN                                  ///
////////////////////////////////////////////////////////////////////////
int main(int argc, char * argv[]) {
	string varsFile, benchmarkName;
	map<string, int> name2IdF;
	map<int, string> id2NameF;
	vector<string> varOrder;

	parseOptionsOrdering(argc, argv);
	benchmarkName = options.benchmark;
	varsFile      = options.varsOrder;

	Abc_Ntk_t* FNtk = getNtk(benchmarkName,true);
	Aig_Man_t* FAig = Abc_NtkToDar(FNtk, 0, 0);

	populateVars(FNtk, varsFile, varOrder,
					varsXF, varsYF,
					name2IdF, id2NameF);

	auto rankAll =  calculateLeastOccurence(FAig);

	vector<pair<int, string> > rankPair;
	for(int i = 0; i < numY; i++)
		rankPair.push_back(make_pair(rankAll[i],varOrder[i]));

	sort(rankPair.begin(), rankPair.end());

	for(auto it: rankPair)
		cout << it.second << endl;

	// Stop ABC
	Abc_Stop();
	return 0;
}
