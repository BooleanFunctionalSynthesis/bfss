#include <iostream>
#include <cstdio>
#include <fstream>
#include <cassert>
#include <string.h>
#include <vector>
#include <set>
#include <map>
#include <queue>
#include <algorithm>
#include <boost/range/adaptor/reversed.hpp>

using namespace std;

#define VERILOG_HEADER "// Generated using findDep.cpp \n"

vector<vector<int> > allClauses;
vector<bool> tseitinClauses;
vector<int> varsX;
vector<int> varsY;
int numVars, numClauses;

vector<set<int> > existsAsPos;
vector<set<int> > existsAsNeg;
vector<map<int,int> > posImplies;
vector<map<int,int> > negImplies;

map<int, vector<int> > depAND;
map<int, vector<int> > depOR;
map<int, vector<int> > depXOR;
set<int> depCONST;
set<int> depTRUE;
set<int> depFALSE;
vector<bool> depFound;

queue<int> litToPropagate;

void readQdimacsFile(char * qdFileName);
void print(vector<int> & v);
void print(set<int> & v);
void findDependencies();
bool findDepAND(int y);
bool findDepOR(int y);
bool findDepXOR(int y);
void findLitToProp();
void propagateLiteral(int lit);
void writeVerilogFile(string fname, string moduleName);
int addConjunctionsToVerilog(ofstream&ofs, int start, int end, int&nextVar);
void writeVariableFile(string fname);
void writeDependenceFile(string fname);
string vecToVerilogLine(vector<int> &v, string op);
void writeNonTseitinToQdimacsFile(string fname);
static inline void addToImpliesMap(map<int,int>&m, int lit, int clauseNum);
static inline void processBinaryClause(int clauseNum);
static inline void setConst(int lit);
static inline map<int,int>& getImpliesMap(int lit);
bool checkForCycles();
bool DFS_checkForCycles(vector<set<int> >& graph, int node, vector<int>& DFS_startTime, vector<int>& DFS_endTime, int& DFS_currTime);

inline string varNumToName(int v) {
	return ("v_"+to_string(v));
}
inline string extraNumToName(int v) {
	return ("x_"+to_string(v));
}
inline bool cannotDependOn(int v) {
	return depFound[abs(v)]==true and
			depCONST.find(abs(v))==depCONST.end() and
			depCONST.find(-abs(v))==depCONST.end();
}

int main(int argc, char * argv[]) {
    char * qdFileName;
    if ( argc < 2 ) {
        cout << "Wrong number of command-line arguments. Usage: readCnf qdimacs_filename " << endl;
        return 1;
    }
    qdFileName = argv[1];

	string baseFileName(qdFileName);
	baseFileName = baseFileName.substr(baseFileName.find_last_of("/") + 1);  //Get the file name;
	baseFileName.erase(baseFileName.find (".qdimacs"), string::npos); //This contains the code for the raw file name;
	cout << "BaseName:     " << baseFileName << endl;

	string varFileName = baseFileName + "_var.txt";
	string aigFileName = baseFileName + ".v" ;
	string depFileName = baseFileName + "_dep.txt" ;
	string qdmFileName = baseFileName + ".qdimacs.noUnary" ;

	readQdimacsFile(qdFileName);
	cout << "Finished readQdimacsFile" << endl;

	// TODO: Propagate unary clauses
	findLitToProp();
	cout << "Finished findLitToProp" << endl;
	while(!litToPropagate.empty()) {
		int toProp = litToPropagate.front();
		litToPropagate.pop();
		propagateLiteral(toProp);
	}
	cout << "Finished propagateLiteral" << endl;

	writeNonTseitinToQdimacsFile(qdmFileName);

	findDependencies();
	cout << "Finished findDependencies" << endl;

	assert(!checkForCycles());
	cout << "Finished checkForCycles" << endl;

	int numNonTseitin = 0;
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			numNonTseitin++;
			// cout<<i<<": \t"; print(allClauses[i]);
		}
	}
	cout << "depCONST.size(): " << depCONST.size() << endl;
	cout << "numNonTseitin:   " << numNonTseitin << endl;

	writeVerilogFile(aigFileName, baseFileName);
	writeVariableFile(varFileName);
	writeDependenceFile(depFileName);
}

void readQdimacsFile(char * qdFileName) {
    char C[100], c;
    int tmpVar;

	FILE *qdFPtr = fopen (qdFileName, "r");

	// Number of variables and clauses
	fscanf (qdFPtr, "%c", &c);
	fscanf (qdFPtr, "%s", C);
	while (strcmp (C, "cnf") != 0)
		fscanf (qdFPtr, "%s", C);
	fscanf(qdFPtr, "%d %d", &numVars, &numClauses); // read first line p cnf
	cout << "NumVar:       " <<  numVars << endl;
	cout << "NumClauses:   " << numClauses << endl;

	// Vars X
	fscanf (qdFPtr, "%c", &c);
	while (c != 'a')
		fscanf (qdFPtr, "%c", &c);
	fscanf(qdFPtr, "%d", &tmpVar);
	while (tmpVar !=0) {
		varsX.push_back(tmpVar);
		fscanf(qdFPtr, "%d", &tmpVar);
	}
	cout << "varsX.size(): " << varsX.size() << endl;
	assert (numVars > varsX.size());

	// Vars Y (to elim)
	fscanf (qdFPtr, "%c", &c);
	while (c != 'e')
		fscanf (qdFPtr, "%c", &c);
	fscanf(qdFPtr, "%d", &tmpVar);
	while (tmpVar !=0) {
		varsY.push_back(tmpVar);
		fscanf(qdFPtr, "%d", &tmpVar);
	}
	cout << "varsY.size(): " << varsY.size() << endl;
	assert (numVars > varsY.size());

	// Update NumVars = maxVar
	int maxVar = 0;
	for(auto it:varsX)
		maxVar = max(maxVar,it);
	for(auto it:varsY)
		maxVar = max(maxVar,it);
	cout << "maxVar:       " << maxVar << endl;
	if(maxVar < numVars) {
		cout << "Setting numVars = " << maxVar << endl;
		numVars = maxVar;
	}

	existsAsPos.resize(numVars+1);
	existsAsNeg.resize(numVars+1);
	posImplies.resize(numVars+1, map<int,int>());
	negImplies.resize(numVars+1, map<int,int>());
	depFound.resize(numVars+1, false);

	// Clauses
	for (int i = 0; i < numClauses ; i++) {
		vector<int> tempClause;
		fscanf(qdFPtr, "%d", &tmpVar);
		while (tmpVar != 0) {
			tempClause.push_back(tmpVar);
			if(tmpVar > 0) { // pos
				existsAsPos[tmpVar].insert(i);
			}
			else { // neg
				existsAsNeg[-tmpVar].insert(i);
			}
			fscanf(qdFPtr, "%d", &tmpVar);
		}
		if(!tempClause.empty()) {
			allClauses.push_back(tempClause);
			tseitinClauses.push_back(false);
		}

		if(tempClause.size() == 2) { // populate ___Implies
			processBinaryClause(allClauses.size()-1);
		}
	}

	fclose (qdFPtr);
}

void findDependencies() {
	// Find AND dependencies
	// for(auto y:varsY) {
	// for(auto it = varsY.rbegin(); it!=varsY.rend(); ++it) {
	// 	int y = *it;
	for(auto y:boost::adaptors::reverse(varsY)) {
		depFound[y] = depFound[y] or findDepAND(y) or findDepOR(y);
	}
	for(auto y:boost::adaptors::reverse(varsY)) {
		depFound[y] = depFound[y] or findDepXOR(y);
	}
}

bool findDepAND(int y) {
	// Check for y = AND(...)
	for(auto clauseNum: existsAsPos[y]) { // Checking all possible clauses

		if(tseitinClauses[clauseNum] == true)
			continue;

		bool gotcha = true;
		bool cyclic = false;
		// cout << "clause "; print(allClauses[clauseNum]);
		for(auto v2: allClauses[clauseNum]) {
			if(tseitinClauses[clauseNum] == true)
				continue;
			if(v2!=y and posImplies[y].find(-v2)==posImplies[y].end()) {
				// cout << "Breaking because of " << v2 << endl;
				gotcha = false;
				break;
			}
			if(v2!=y and cannotDependOn(v2)) {
				cyclic = true;
			}
		}
		if(gotcha) {
			// if(cyclic)
			// 	cout << "Skipping AND because of possible cyclic dependency" << endl;
			// else{
				// Print it
				string dep = "AND(";
				for(auto v2: allClauses[clauseNum]) {
					if(tseitinClauses[clauseNum] == true)
						continue;
					if(v2!=y) {
						dep = dep + to_string(-v2) + ", ";
					}
				}
				dep = dep.substr(0,dep.length()-2) + ")";
				cout << "DEP" << y << " = " << dep << endl;

				// Found Dependency
				// assert(depAND.find(y) == depAND.end());
				depAND[y] = vector<int>();
				for(auto v2: allClauses[clauseNum]) {
					if(tseitinClauses[clauseNum] == true)
						continue;
					if(v2!=y) {
						depAND[y].push_back(v2);
						tseitinClauses[posImplies[y][-v2]] = true; // tseitinClauses=true
					}
				}
				tseitinClauses[clauseNum] = true; // tseitinClauses=true
				return true;
			// }
		}
	}
	return false;
}

bool findDepOR(int y) {
	// Check for -y = AND(...)
	for(auto clauseNum: existsAsNeg[y]) { // Checking all possible clauses

		if(tseitinClauses[clauseNum] == true)
			continue;

		bool gotcha = true;
		bool cyclic = false;
		// cout << "clause "; print(allClauses[clauseNum]);
		for(auto v2: allClauses[clauseNum]) {
			if(tseitinClauses[clauseNum] == true)
				continue;
			if(v2!=-y and negImplies[y].find(-v2)==negImplies[y].end()) {
				// cout << "Breaking because of " << v2 << endl;
				gotcha = false;
				break;
			}
			if(v2!=y and cannotDependOn(v2)) {
				cyclic = true;
			}
		}
		if(gotcha) {
			// if(cyclic)
			// 	cout << "Skipping OR because of possible cyclic dependency" << endl;
			// else {
				// Print it
				string dep = "OR(";
				for(auto v2: allClauses[clauseNum]) {
					if(tseitinClauses[clauseNum] == true)
						continue;
					if(v2!=-y) {
						dep = dep + to_string(v2) + ", ";
					}
				}
				dep = dep.substr(0,dep.length()-2) + ")";
				cout << "DEP" << y << " = " << dep << endl;

				// Found Dependency
				// assert(depOR.find(y) == depOR.end());
				depOR[y] = vector<int>();
				for(auto v2: allClauses[clauseNum]) {
					if(tseitinClauses[clauseNum] == true)
						continue;
					if(v2!=-y) {
						depOR[y].push_back(v2);
						tseitinClauses[negImplies[y][-v2]] = true; // tseitinClauses=true
					}
				}
				tseitinClauses[clauseNum] = true; // tseitinClauses=true
				return true;
			// }
		}
	}
	return false;
}

bool findDepXOR(int y) {
	// Check for y = XOR(...)
	for(auto clauseNum: existsAsPos[y]) { // Checking all possible clauses

		auto & cl1 = allClauses[clauseNum];
		if(tseitinClauses[clauseNum] == true or cl1.size()!=3)
			continue;

		int iTemp = 0;
		vector<int> otherVars(2);
		if(cl1[iTemp]==y)
			iTemp++;
		otherVars[0] = cl1[iTemp];
		iTemp++;
		if(cl1[iTemp]==y)
			iTemp++;
		otherVars[1] = cl1[iTemp];
		iTemp++;

		for(auto clauseNum2: existsAsPos[y]) { // Checking all possible clauses

			auto & cl2 = allClauses[clauseNum2];
			if(tseitinClauses[clauseNum2] == true or cl2.size()!=3
				or clauseNum==clauseNum2)
				continue;

			if(find(cl2.begin(),cl2.end(),-otherVars[0])!=cl2.end()
				and find(cl2.begin(),cl2.end(),-otherVars[1])!=cl2.end()) {

				int clause1foundAt = -1;
				int clause2foundAt = -1;
				for(auto clauseNum3: existsAsNeg[y]) { // Checking all possible clauses
					auto & cl3 = allClauses[clauseNum3];
					if(tseitinClauses[clauseNum3] == true or cl3.size()!=3
						or clauseNum3==clauseNum2 or clauseNum3==clauseNum)
						continue;

					if(find(cl3.begin(),cl3.end(),otherVars[0])!=cl3.end()
						and find(cl3.begin(),cl3.end(),-otherVars[1])!=cl3.end()) {
						clause1foundAt = clauseNum3;
					}
					if(find(cl3.begin(),cl3.end(),-otherVars[0])!=cl3.end()
						and find(cl3.begin(),cl3.end(),otherVars[1])!=cl3.end()) {
						clause2foundAt = clauseNum3;
					}
				}
				if(clause1foundAt != -1 and clause2foundAt != -1) {
					// if(!cannotDependOn(otherVars[0]) and !cannotDependOn(otherVars[1])) {
						// Print it
						string dep = "XOR(" + to_string(otherVars[0]) + ", " + to_string(-otherVars[1]) + ")";
						cout << "DEP" << y << " = " << dep << endl;

						// Found Dependency
						vector<int> res(2);
						res[0] = otherVars[0];
						res[1] = -otherVars[1];
						depXOR[y] = res;

						tseitinClauses[clauseNum] = true;	// tseitinClauses=true
						tseitinClauses[clauseNum2] = true;	// tseitinClauses=true
						tseitinClauses[clause1foundAt] = true;	// tseitinClauses=true
						tseitinClauses[clause2foundAt] = true;	// tseitinClauses=true

						return true;
					// }
					// else {
					// 	cout << "Skipping XOR because of possible cyclic dependency" << endl;
					// }
				}
			}
		}
	}
	return false;
}

void print(vector<int> & v) {
	for(auto it:v)
		cout << it << " ";
	cout << endl;
}

void print(map<int, int> & v) {
	for(auto it:v)
		cout << "(" << it.first << "," << it.second << ") ";
	cout << endl;
}

void print(set<int> & v) {
	for(auto it:v)
		cout << it << " ";
	cout << endl;
}

void findLitToProp() {
	for(int clauseNum = 0; clauseNum < allClauses.size(); clauseNum++) {
		auto & clause = allClauses[clauseNum];
		if(clause.size() == 1) {
			setConst(clause[0]);
			tseitinClauses[clauseNum] = true; // Unary tseitinClauses=true
		}
		else if(clause.size() == 2) {
			int v0 = clause[0];
			int v1 = clause[1];

			// -v1 -> v0, check if v1 -> v0, then v0_isConst
			// -v0 -> v1, check if v0 -> v1, then v1_isConst

			map<int,int>& v0_map = getImpliesMap(v0);
			map<int,int>& v1_map = getImpliesMap(v1);

			if(v1_map.find(v0) != v1_map.end()) { // v0_isConst
				// cout << "clause: "; print(clause);
				setConst(v0);
				tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
				tseitinClauses[v1_map[v0]] = true;	// Unary tseitinClauses=true
			}
			if(v0_map.find(v1) != v0_map.end()) { // v1_isConst
				// cout << "clause: "; print(clause);
				setConst(v1);
				tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
				tseitinClauses[v0_map[v1]] = true;	// Unary tseitinClauses=true
			}
		}
	}
}

void propagateLiteral(int lit) {
	int var = abs(lit);
	bool pos = lit>0;
	for(auto clauseNum:existsAsPos[var]) {
		if(tseitinClauses[clauseNum])
			continue;
		if(pos) {
			tseitinClauses[clauseNum] = true;	// tseitinClauses=true
		}
		else{
			// Remove var from allClauses
			auto it = find(allClauses[clauseNum].begin(), allClauses[clauseNum].end(), var);
			assert(it != allClauses[clauseNum].end());
			*it = allClauses[clauseNum].back();
			allClauses[clauseNum].resize(allClauses[clauseNum].size()-1);

			assert(!allClauses[clauseNum].empty()); // CNF formula is unsat
			if(allClauses[clauseNum].size() == 1) {
				setConst(allClauses[clauseNum][0]);
				tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
			}
			else if(allClauses[clauseNum].size() == 2) {
				processBinaryClause(clauseNum);
			}
		}
	}

	for(auto clauseNum:existsAsNeg[var]) {
		if(tseitinClauses[clauseNum])
			continue;
		if(!pos) {
			tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
		}
		else{
			// Remove var from allClauses
			auto it = find(allClauses[clauseNum].begin(), allClauses[clauseNum].end(), -var);
			assert(it != allClauses[clauseNum].end());
			*it = allClauses[clauseNum].back();
			allClauses[clauseNum].resize(allClauses[clauseNum].size()-1);

			assert(!allClauses[clauseNum].empty()); // CNF formula is unsat
			if(allClauses[clauseNum].size() == 1) {
				setConst(allClauses[clauseNum][0]);
				tseitinClauses[clauseNum] = true;	// Unary tseitinClauses=true
			}
			else if(allClauses[clauseNum].size() == 2) {
				processBinaryClause(clauseNum);
			}
		}
	}

	if(pos) {
		existsAsNeg[var].clear();
	}
	else{
		existsAsPos[var].clear();
	}
}

void writeVerilogFile(string fname, string moduleName) {
	ofstream ofs (fname, ofstream::out);
	ofs << VERILOG_HEADER;
	ofs << "module " << moduleName << " ";
	ofs << "(";
	for(auto it:varsX) {
		ofs << varNumToName(it) << ", ";
	}
	for(auto it:varsY) {
		if(!depFound[it])
			ofs << varNumToName(it) << ", ";
	}
	ofs << "o_1);" << endl;

	// Input/Output/Wire
	for(auto it:varsX) {
		assert(!depFound[it]);
		ofs << "input " << varNumToName(it) << ";\n";
	}
	for(auto it:varsY) {
		if(!depFound[it])
			ofs << "input " << varNumToName(it) << ";\n";
	}
	ofs << "output o_1;\n";
	for(auto it:varsY) {
		if(depFound[it])
			ofs << "wire " << varNumToName(it) << ";\n";
	}

	// Extra wires required for non-tseitin clauses
	int numNonTseitin = 0;
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			numNonTseitin++;
		}
	}
	assert(numNonTseitin > 0);
	for(int i = 1; i<2*numNonTseitin; i++) {
		ofs << "wire " << extraNumToName(i) << ";\n";
	}


	// Assign Dependencies
	// constants
	for(auto it: depCONST) {
		int var = abs(it);
		bool pos = it>0;
		ofs << "assign " << varNumToName(var) << " = " << (pos?1:0) << ";\n";
	}
	// and
	for(auto&it: depAND) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"&");
		ofs << "assign " << varNumToName(it.first) << " = " << res << ";\n";
	}
	// or
	for(auto&it: depOR) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"|");
		ofs << "assign " << varNumToName(it.first) << " = " << res << ";\n";
	}
	// xor
	for(auto&it: depXOR) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"^");
		ofs << "assign " << varNumToName(it.first) << " = " << res << ";\n";
	}

	// Assign Non-tseitin dependencies
	int eNum = 1;
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			string res = vecToVerilogLine(allClauses[i],"|");
			ofs << "assign " << extraNumToName(eNum) << " = " << res << ";\n";
			eNum++;
		}
	}
	assert(eNum == numNonTseitin+1);

	// Conjunct all Extra Variables (x_1 .. x_numNonTseitin)
	int finalVar =  addConjunctionsToVerilog(ofs, 1, numNonTseitin, eNum);
	assert(finalVar <= 2*numNonTseitin);

	ofs << "assign o_1 = " << extraNumToName(finalVar) << ";\n";
	ofs << "endmodule\n";
	ofs.close();
}

int addConjunctionsToVerilog(ofstream&ofs, int start, int end, int&nextVar) {
	assert(start<=end);
	if(start==end)
		return start;

	int mid = (start+end+1)/2 - 1;
	int v1 = addConjunctionsToVerilog(ofs, start, mid, nextVar);
	int v2 = addConjunctionsToVerilog(ofs, mid+1, end, nextVar);

	string res = extraNumToName(v1) + " & " + extraNumToName(v2);
	ofs << "assign " << extraNumToName(nextVar) << " = " << res << ";\n";
	nextVar++;
	return nextVar-1;
}

void writeVariableFile(string fname) {
	ofstream ofs (fname, ofstream::out);

	for(auto it:varsY) {
		if(!depFound[it])
			ofs << varNumToName(it) << "\n";
	}

	ofs.close();
}

void writeDependenceFile(string fname) {
	ofstream ofs (fname, ofstream::out);
	// Assign Dependencies
	// constants
	for(auto it: depCONST) {
		int var = abs(it);
		bool pos = it>0;
		ofs << varNumToName(var) << " = " << (pos?1:0) << ";\n";
	}
	// and
	for(auto&it: depAND) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"&");
		ofs << varNumToName(it.first) << " = " << res << ";\n";
	}
	// or
	for(auto&it: depOR) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"|");
		ofs << varNumToName(it.first) << " = " << res << ";\n";
	}
	// xor
	for(auto&it: depXOR) {
		int var = abs(it.first);
		bool pos = it.first>0;
		string res = vecToVerilogLine(it.second,"^");
		ofs << varNumToName(it.first) << " = " << res << ";\n";
	}
	ofs.close();
}

string vecToVerilogLine(vector<int> &v, string op) {
	string res;
	for(auto el:v) {
		if(el > 0)
			res = res + varNumToName(abs(el)) + " " + op + " ";
		else
			res = res + "~" + varNumToName(abs(el)) + " " + op + " ";
	}
	return res.substr(0,res.length()-2-op.length());
}

void writeNonTseitinToQdimacsFile(string fname) {
	ofstream ofs (fname, ofstream::out);

	// Extra wires required for non-tseitin clauses
	int numNonTseitin = 0;
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			numNonTseitin++;
		}
	}

	ofs << VERILOG_HEADER;
	ofs << "p cnf " << numVars << " " << numNonTseitin+depCONST.size() << endl;

	ofs << "a ";
	for(auto it:varsX) {
		ofs << it << " ";
	}
	ofs << 0 << endl;

	ofs << "e ";
	for(auto it:varsY) {
		if(!depFound[it])
			ofs << it << " ";
	}
	ofs << 0 << endl;

	// constants
	for(auto it: depCONST) {
		ofs << it << " 0 \n";
	}

	// Non-tseitin clauses
	for(int i = 0; i < allClauses.size(); i++) {
		if(!tseitinClauses[i]) {
			for(auto el: allClauses[i]) {
				ofs << el << " ";
			}
			ofs << "0\n";
		}
	}

	ofs.close();
}

static inline map<int,int>& getImpliesMap(int lit) {
	return (lit>0)?posImplies[lit]:negImplies[-lit];
}

static inline void addToImpliesMap(map<int,int>&m, int lit, int clauseNum) {
	auto it = m.find(lit);
	if(it == m.end()) {
		m[lit] = clauseNum;
	}
	else if(it->second != clauseNum) { // set clauseNum is redundant
		tseitinClauses[clauseNum] = true;
	}
}

static inline void setConst(int lit) {
	cout << "DEPConst " << lit << endl;
	depFound[abs(lit)] = true;
	depCONST.insert(lit);
	litToPropagate.push(lit);
}

static inline void processBinaryClause(int clauseNum) {
	vector<int>&clause  = allClauses[clauseNum];
	assert(clause.size() == 2);
	int v0 = clause[0];
	int v1 = clause[1];

	map<int,int>& v0_map = getImpliesMap(-v0);
	map<int,int>& v1_map = getImpliesMap(-v1);

	addToImpliesMap(v0_map, v1, clauseNum);
	addToImpliesMap(v1_map, v0, clauseNum);
}

bool checkForCycles() {
	vector<set<int> > graph(numVars+1);
	
	// Create Graph
	for(auto it: depCONST) {
		int var = abs(it);
		graph[var].insert(0);
	}
	for(auto&it: depAND) {
		int var = abs(it.first);
		for(auto&it2:it.second)
			graph[var].insert(abs(it2));
	}
	for(auto&it: depOR) {
		int var = abs(it.first);
		for(auto&it2:it.second)
			graph[var].insert(abs(it2));
	}
	for(auto&it: depXOR) {
		int var = abs(it.first);
		for(auto&it2:it.second)
			graph[var].insert(abs(it2));
	}

	vector<int> DFS_startTime(numVars+1,-1);
	vector<int> DFS_endTime(numVars+1,-1);
	int DFS_currTime = 0;

	for (int i = 0; i < numVars + 1; ++i) {
		if(DFS_startTime[i] == -1) {
			if(DFS_checkForCycles(graph, i, DFS_startTime, DFS_endTime, DFS_currTime)) {
				cout << i << endl;
				return true;
			}
		}
	}
	return false;
}

bool DFS_checkForCycles(vector<set<int> >& graph, int node, vector<int>& DFS_startTime, vector<int>& DFS_endTime, int& DFS_currTime) {
	if(DFS_startTime[node] != -1) {
		if(DFS_endTime[node] == -1) {
			// Back Edge
			cout << "Found dependency cycle: ";
			return true;
		}
		else {
			// Cross Edge
			return false;
		}
	}
	// Forward Edge
	DFS_startTime[node] = DFS_currTime++;

	for(auto it:graph[node]) {
		if(DFS_checkForCycles(graph, it, DFS_startTime, DFS_endTime, DFS_currTime)) {
			cout << it << " ";
			return true;
		}
	}

	DFS_endTime[node] = DFS_currTime++;
	return false;
}
