#include "nnf.h"
#include <numeric>

Nnf_Obj::Nnf_Obj(int id) : Nnf_Obj(id, NNF_OBJ_NONE) {};
Nnf_Obj::Nnf_Obj(int id, Nnf_Type t) : Id(id), Type(t), neg(NULL), pFanin0(NULL), pFanin1(NULL), AigNum(-1), fMarkA(false), pData(NULL) {};

void Nnf_Obj::print()
{
    printf("Node %d : ", Nnf_ObjId(this));
    if (Nnf_ObjIsConst1(this))
        printf("constant 1");
    else if (Nnf_ObjIsCiPos(this))
        printf("CI pos");
    else if (Nnf_ObjIsCiNeg(this))
        printf("CI neg");
    else if (Nnf_ObjIsCo(this))
        printf("CO( %d%s )", Nnf_ObjFanin0(this)->Id, (Nnf_ObjFaninC0(this)? "\'" : " "));
    else if (Nnf_ObjIsAnd(this))
        printf("AND( %d%s, %d%s )",
            Nnf_ObjFanin0(this)->Id, (Nnf_ObjFaninC0(this)? "\'" : " "),
            Nnf_ObjFanin1(this)->Id, (Nnf_ObjFaninC1(this)? "\'" : " "));
    else if ( Nnf_ObjIsOr(this))
        printf(" OR( %d%s, %d%s )",
            Nnf_ObjFanin0(this)->Id, (Nnf_ObjFaninC0(this)? "\'" : " "),
            Nnf_ObjFanin1(this)->Id, (Nnf_ObjFaninC1(this)? "\'" : " "));
    else
        assert(false);
    printf(" (refs = %3d)\n", Nnf_ObjRefs(this));
}

int Nnf_Obj::getNumRef()
{
	return pFanoutPos.size() + pFanoutNeg.size();
}

Nnf_Man::Nnf_Man() : pName("No_Name") {
	this->pConst1 = createNode(NNF_OBJ_CONST1);
}

Nnf_Man::Nnf_Man(Aig_Man_t* pSrc) : Nnf_Man() {
	init(pSrc);
}

Nnf_Man::Nnf_Man(DdManager* ddMan, DdNode* FddNode) : Nnf_Man() {
	init(ddMan, FddNode);
}

void Nnf_Man::init(Aig_Man_t* pSrc) {
	assert(_allNodes.size()==1);
	assert(getCiNum()==0);
	assert(getCoNum()==0);
	// cout <<"\n\nInitially" << endl;
	// print();

	int rem = Aig_ManCleanup(pSrc);
	cout << "Removed " << rem << " nodes during NNF cleanup" << endl;

	// cout <<"\n\nParsing..." << endl;
	parse_aig(pSrc);

	// cout <<"\n\nParsed Aig" << endl;
	// print();
	makeNnf();

	// cout <<"\n\nPushed Bubbles down" << endl;
	// print();
	Nnf_ManTopoId();

	// cout <<"\n\nTopo-sorted" << endl;
	// print();
}

void Nnf_Man::init(DdManager* ddMan, DdNode* FddNode) {
	assert(_allNodes.size()==1);
	assert(getCiNum()==0);
	assert(getCoNum()==0);
	// First Create All Leaves (Input Nodes)
	int numCi = Cudd_ReadSize(ddMan);
	for (int i = 0; i < numCi; ++i) {
		Nnf_Obj* ci = this->createCi();
		ci->OrigAigId = i+1;	// @TODO: FIX!
	}

	// Recursively convert to nnf
	map<DdNode*, Nnf_Obj*> cache;
	Nnf_Obj* head = this->bdd2nnf_rec(FddNode, cache);
	this->createCo(head);

	// Check isNNF
	assert(this->checkIsNnf());
}

bool Nnf_Man::checkIsNnf() {
	// Unmark all nodes
	for(auto it: _allNodes)
		Nnf_ObjClearMarkA(it);

	bool res = true;
	for(auto it:_outputs) {
		if(!checkIsNnf_rec(it)) {
			res = false;
			break;
		}
	}

	// Unmark all nodes
	for(auto it: _allNodes)
	Nnf_ObjClearMarkA(it);

	return res;
}

bool Nnf_Man::checkIsNnf_rec(Nnf_Obj* pObj) {
	if(Nnf_ObjIsMarkA(pObj))
		return true;
	Nnf_ObjSetMarkA(pObj);

	if(Nnf_IsComplement(pObj)) {
		assert(!Nnf_ObjIsConst0(pObj));
		return false;
	}
	else if(Nnf_ObjIsConst1(pObj)
		or Nnf_ObjIsCiPos(pObj)
		or Nnf_ObjIsCiNeg(pObj)) {
		return true;
	}
	else if(Nnf_ObjIsCo(pObj)) {
		return this->checkIsNnf_rec(Nnf_ObjFanin0(pObj));
	}
	else if(Nnf_ObjIsAnd(pObj) or Nnf_ObjIsOr(pObj)) {
		return (this->checkIsNnf_rec(Nnf_ObjFanin0(pObj))
			and this->checkIsNnf_rec(Nnf_ObjFanin1(pObj)));
	}
	else
		assert(false);
}

Nnf_Obj* Nnf_Man::bdd2nnf_rec(DdNode* FddNode, map<DdNode*, Nnf_Obj*>&cache) {

	if(cache.count(FddNode) > 0)
		return cache[FddNode];

	Nnf_Obj* res;

	if Cudd_IsConstant(FddNode) {
		bool isConst1 = Cudd_V(FddNode);
		if(isConst1) // res = 1-node;
			res = Nnf_NotCond(this->const1(), Cudd_IsComplement(FddNode));
		else // res = 0-node;
			res = Nnf_NotCond(this->const0(), Cudd_IsComplement(FddNode));
	} else {

		// Find NNF variable corresponding to FddNode
		int varNum = Cudd_Regular(FddNode)->index;
		Nnf_Obj* Xi = this->getCiPos(varNum);
		Nnf_Obj* Xi_bar = this->getCiNeg(varNum);

		if(Cudd_IsComplement(FddNode)) {
			// res = (-tc and Xi) or (-ec and -Xi)
			Nnf_Obj* tc = this->bdd2nnf_rec(Cudd_Not(Cudd_T(FddNode)), cache);
			Nnf_Obj* ec = this->bdd2nnf_rec(Cudd_Not(Cudd_E(FddNode)), cache);
			res = Nnf_Or(Nnf_And(tc, Xi), Nnf_And(ec, Xi_bar));
		}
		else {
			// res = (tc and Xi) or (ec and -Xi)
			Nnf_Obj* tc = this->bdd2nnf_rec(Cudd_T(FddNode), cache);
			Nnf_Obj* ec = this->bdd2nnf_rec(Cudd_E(FddNode), cache);
			res = Nnf_Or(Nnf_And(tc, Xi), Nnf_And(ec, Xi_bar));
		}
	}

	// printf("bdd2nnf_rec %s%d -> ",(Cudd_IsComplement(FddNode)?"-":" "),Cudd_Regular(FddNode)->Id);
	// cout << (Nnf_IsComplement(res)?"-":" ");
	// Nnf_Regular(res)->print();
	cache[FddNode] = res;
	return res;
}

Nnf_Man::~Nnf_Man() {
	for(auto it: _allNodes) {
		if(it!=NULL)
			delete it;
	}
}

Nnf_Obj* Nnf_Man::Nnf_And(Nnf_Obj* left, Nnf_Obj* right) {
	if(Nnf_ObjIsConst1(left)) return right;
	if(Nnf_ObjIsConst1(right)) return left;
	if(Nnf_ObjIsConst0(left)) return this->const0();
	if(Nnf_ObjIsConst0(right)) return this->const0();

	Nnf_Obj* newNode = this->createNode(NNF_OBJ_AND);
	NNf_ObjSetFanin0(newNode, left);
	NNf_ObjSetFanin1(newNode, right);

	return newNode;
}

Nnf_Obj* Nnf_Man::Nnf_Or(Nnf_Obj* left, Nnf_Obj* right) {
	if(Nnf_ObjIsConst1(left)) return this->const1();
	if(Nnf_ObjIsConst1(right)) return this->const1();
	if(Nnf_ObjIsConst0(left)) return right;
	if(Nnf_ObjIsConst0(right)) return left;

	Nnf_Obj* newNode = this->createNode(NNF_OBJ_OR);
	NNf_ObjSetFanin0(newNode, left);
	NNf_ObjSetFanin1(newNode, right);

	return newNode;
}

Nnf_Obj* Nnf_Man::getCiPos(int i) {return _inputs_pos[i];}
Nnf_Obj* Nnf_Man::getCiNeg(int i) {return _inputs_neg[i];}
Nnf_Obj* Nnf_Man::getCo(int i) {return _outputs[i];}
Nnf_Obj* Nnf_Man::getObj(int i) {return _allNodes[i];}
int      Nnf_Man::getCiNum() {return _inputs_pos.size();}
int      Nnf_Man::getCoNum() {return _outputs.size();}
Nnf_Obj* Nnf_Man::const0() {return Nnf_Not(pConst1);}
Nnf_Obj* Nnf_Man::const1() {return pConst1;}

int Nnf_Man::getNewAigNodeID(int origAigNodeId) {
	if(_origToNewNodeId.count(origAigNodeId) == 0)
		return -1; // Not Found
	else
		return _origToNewNodeId[origAigNodeId];
}

Nnf_Obj* Nnf_Man::createNode(Nnf_Type t) {
	int id = _allNodes.size();
	Nnf_Obj* obj = new Nnf_Obj(id, t);
	assert(obj != NULL);
	_allNodes.push_back(obj);
	return obj;
}

// Returns positive input
Nnf_Obj* Nnf_Man::createCi() {
	Nnf_Obj* pos = createNode(NNF_OBJ_CI_POS);
	Nnf_Obj* neg = createNode(NNF_OBJ_CI_NEG);
	assert(pos!=NULL);
	assert(neg!=NULL);
	pos->neg = neg;
	neg->neg = pos;
	_inputs_pos.push_back(pos);
	_inputs_neg.push_back(neg);
	return pos;
}

Nnf_Obj* Nnf_Man::createCo(Nnf_Obj* pDriver) {
	Nnf_Obj* co = createNode(NNF_OBJ_CO);
	assert(co != NULL);
	NNf_ObjSetFanin0(co, pDriver);
	_outputs.push_back(co);
	return co;
}

void Nnf_Man::parse_aig(Aig_Man_t* pSrc) {
	int i;
	Aig_Obj_t* pObj, *f0, *f1;
	Nnf_Obj* nObj;

	if(pSrc->pName)
		this->pName = string(pSrc->pName);

	// Delete Current Nodes
	for (int i = 1; i < _allNodes.size(); ++i) {
		if(_allNodes[i] != NULL)
			delete _allNodes[i];
			_allNodes[i] = NULL;
	}
	_allNodes.resize(1);
	_inputs_pos.clear();
	_inputs_neg.clear();
	_outputs.clear();

	Aig_ManForEachObj( pSrc, pObj, i ) {
		if(Aig_ObjIsConst1(pObj)) {
			nObj = this->pConst1;
			nObj->OrigAigId = pObj->Id;
			pObj->pData = nObj;
		}
		else if(Aig_ObjIsCi(pObj)) {
			nObj = this->createCi();
			nObj->OrigAigId = pObj->Id;
			pObj->pData = nObj;
		}
		else if(Aig_ObjIsCo(pObj)) {
			Nnf_Obj* child = (Nnf_Obj*) Aig_ObjFanin0(pObj)->pData;
			child = Nnf_NotCond(child, Aig_ObjFaninC0(pObj));
			nObj = this->createCo(child);
			nObj->OrigAigId = pObj->Id;
			pObj->pData = nObj;
		}
		else if(Aig_ObjIsAnd(pObj)) {
			Nnf_Obj* child0, *child1;
			if(Aig_ObjFanin0(pObj)) {
				child0 = (Nnf_Obj*) Aig_ObjFanin0(pObj)->pData;
				child0 = Nnf_NotCond(child0, Aig_ObjFaninC0(pObj));
			}
			else {
				child0 = NULL;
			}
			if(Aig_ObjFanin1(pObj)) {
				child1 = (Nnf_Obj*) Aig_ObjFanin1(pObj)->pData;
				child1 = Nnf_NotCond(child1, Aig_ObjFaninC1(pObj));
			}
			else {
				child1 = NULL;
			}

			nObj = this->createNode(NNF_OBJ_AND);
			NNf_ObjSetFanin0(nObj, child0);
			NNf_ObjSetFanin1(nObj, child1);
			nObj->OrigAigId = pObj->Id;
			pObj->pData = nObj;
		}
		else {
			assert(false);
		}
	}
}

void Nnf_Man::makeNnf() {
	for(int i = _allNodes.size()-1; i>=0; i--) {
		pushBubblesDown(_allNodes[i]);
	}
}

void Nnf_Man::pushBubblesDown(Nnf_Obj* nObj) {
	assert(!Nnf_IsComplement(nObj));

	if(Nnf_ObjIsConst1(nObj)) {
		// Nothing to do
		return;
	}

	Nnf_Obj* negObj = nObj->neg;
	int nRefPos = Nnf_ObjRefsPos(nObj);
	int nRefNeg = Nnf_ObjRefsNeg(nObj);

	if(nRefPos>0 && nRefNeg>0) {
		// Need to split
		if(negObj == NULL) {
			// Create neg object if doesn't exist (For nodes other than inputs)
			negObj = createNode(SwitchAndOrType(nObj->Type));
			nObj->neg = negObj;
			negObj->neg = nObj;
			NNf_ObjSetFanin0(negObj, Nnf_Not(Nnf_ObjChild0(nObj)));
			NNf_ObjSetFanin1(negObj, Nnf_Not(Nnf_ObjChild1(nObj)));
		}
		while(!nObj->pFanoutNeg.empty()) {
			Nnf_Obj* parent = *(nObj->pFanoutNeg.begin());
			if(Nnf_ObjChild0(parent) == Nnf_Not(nObj))
				NNf_ObjSetFanin0(parent, negObj);
			if(Nnf_ObjChild1(parent) == Nnf_Not(nObj))
				NNf_ObjSetFanin1(parent, negObj);
		}
	}
	else if(nRefPos>0 && nRefNeg==0) {
		// Nothing to do
	}
	else if(nRefPos==0 && nRefNeg>0) {
		// Switch sign if not input
		if(negObj == NULL) {
			// switch sign
			negObj = nObj;
			nObj->Type = SwitchAndOrType(nObj->Type);
			NNf_ObjSetFanin0(nObj, Nnf_Not(Nnf_ObjChild0(nObj)));
			NNf_ObjSetFanin1(nObj, Nnf_Not(Nnf_ObjChild1(nObj)));
		}
		while(!nObj->pFanoutNeg.empty()) {
			Nnf_Obj* parent = *(nObj->pFanoutNeg.begin());
			if(Nnf_ObjChild0(parent) == Nnf_Not(nObj))
				NNf_ObjSetFanin0(parent, negObj);
			if(Nnf_ObjChild1(parent) == Nnf_Not(nObj))
				NNf_ObjSetFanin1(parent, negObj);
		}
	}
	else if(nRefPos==0 && nRefNeg==0) {
		// Nothing to do
	}
	else {
		assert(false);
	}
}

void Nnf_Man::print() {
	for(auto node: _allNodes) {
		if(node!=NULL) {
			node->print();
		}
	}
}

Aig_Man_t* Nnf_Man::createAigWithClouds() {return createAig(true);}
Aig_Man_t* Nnf_Man::createAigWithoutClouds() {return createAig(false);}

// assumes topo-sorted nodes in NNF
// Objs are ordered as:
// x1 x1' x2 x2' ... xn xn' ... cloud1 ... cloud2 ... cloud3 ...
// Note that (CioId != Id+1) for cloud nodes
Aig_Man_t* Nnf_Man::createAig(bool withCloudInputs) {
	int nNodesMax = 1e5;
	Aig_Man_t* pMan = Aig_ManStart(nNodesMax);

	// Save Name
	pMan->pName = Abc_UtilStrsav((char*)this->pName.c_str());

	Aig_Obj_t* pObj;
	vector<int> CiPosIth;
	vector<int> CiNegIth;
	vector<int> CiCloudIth;
	vector<int> CoIth;

	// Clear Id mappings
	_origToNewNodeId.clear();

	// Ordering Cis
	for(auto node: _inputs_pos) {
		pObj = Aig_ObjCreateCi(pMan);
		CiPosIth.push_back(Aig_ObjCioId(pObj));
		node->AigNum = Aig_ObjCioId(pObj);
		node->pData = pObj;

		// Build InputID map (original -> new)
		_origToNewNodeId[node->OrigAigId] = pObj->Id;
	}
	for(auto node: _inputs_neg) {
		pObj = Aig_ObjCreateCi(pMan);
		CiNegIth.push_back(Aig_ObjCioId(pObj));
		node->AigNum = Aig_ObjCioId(pObj);
		node->pData = pObj;
	}

	for(auto node: _allNodes) {
		if (Nnf_ObjIsConst1(node)) {
			node->pData = Aig_ManConst1(pMan);
		}
		else if (Nnf_ObjIsCiPos(node)) {
			// Handled before
		}
		else if (Nnf_ObjIsCiNeg(node)) {
			// Handled before
		}
		else if (Nnf_ObjIsCo(node)) {
			Aig_Obj_t* child = (Aig_Obj_t*) Nnf_ObjFanin0(node)->pData;
			assert(!Nnf_ObjFaninC0(node));
			pObj = Aig_ObjCreateCo(pMan, child);
			CoIth.push_back(Aig_ObjCioId(pObj));
			node->AigNum = Nnf_ObjFanin0(node)->AigNum;
			node->pData = pObj;
		}
		else if (Nnf_ObjIsAnd(node) || Nnf_ObjIsOr(node)) {
			Aig_Obj_t* child0 = (Aig_Obj_t*) Nnf_ObjFanin0(node)->pData;
			assert(!Nnf_ObjFaninC0(node));
			Aig_Obj_t* child1 = (Aig_Obj_t*) Nnf_ObjFanin1(node)->pData;
			assert(!Nnf_ObjFaninC1(node));

			if (Nnf_ObjIsAnd(node))
				pObj = Aig_And(pMan, child0, child1);
			else
				pObj = Aig_Or(pMan, child0, child1);

			// Create Cloud
			if(withCloudInputs) {
				Aig_Obj_t* cloudObj = Aig_ObjCreateCi(pMan);
				CiCloudIth.push_back(Aig_ObjCioId(cloudObj));
				node->AigNum = Aig_ObjCioId(cloudObj);
				pObj = Aig_And(pMan, pObj, cloudObj);
			}

			node->pData = pObj;
		}
		else {
			assert(false);
		}
	}

	return pMan;
}

// assumes topo-sorted 	nodes in NNF
// Objs are ordered as:
// x1 x1' x2 x2' ... xn xn' ... c1.1 .. c1.2 .. c1.|Y| ... c2.1 .. c2.2 .. c2.|Y| ...
// Note that (CioId != Id+1) for cloud nodes
Aig_Man_t* Nnf_Man::createAigMultipleClouds(int numCloudSets,
	vector<vector<int>> CiCloudIth,
	vector<vector<int>> CoIth) {

	int nNodesMax = 1e5;
	Aig_Man_t* pMan = Aig_ManStart(nNodesMax);

	Aig_Obj_t* pObj;
	vector<int> CiPosIth;
	vector<int> CiNegIth;

	CoIth.clear();
	CoIth.resize(numCloudSets);
	CiCloudIth.clear();
	CiCloudIth.resize(numCloudSets);

	// Clear Id mappings
	_origToNewNodeId.clear();

	// Ordering Cis
	for(auto node: _inputs_pos) {
		pObj = Aig_ObjCreateCi(pMan);
		CiPosIth.push_back(Aig_ObjCioId(pObj));
		node->pData = new vector<Aig_Obj_t*>(numCloudSets, pObj);

		// Build InputID map (original -> new)
		_origToNewNodeId[node->OrigAigId] = pObj->Id;
	}
	for(auto node: _inputs_neg) {
		pObj = Aig_ObjCreateCi(pMan);
		CiNegIth.push_back(Aig_ObjCioId(pObj));
		node->pData = new vector<Aig_Obj_t*>(numCloudSets, pObj);
	}

	for(auto node: _allNodes) {
		if (Nnf_ObjIsConst1(node)) {
			node->pData = new vector<Aig_Obj_t*>(numCloudSets, Aig_ManConst1(pMan));
		}
		else if (Nnf_ObjIsCiPos(node)) {
			// Handled before
		}
		else if (Nnf_ObjIsCiNeg(node)) {
			// Handled before
		}
		else if (Nnf_ObjIsCo(node)) {
			vector<Aig_Obj_t*>* childVec = (vector<Aig_Obj_t*>*) Nnf_ObjFanin0(node)->pData;
			assert(!Nnf_ObjFaninC0(node));
			assert(childVec->size() == numCloudSets);

			node->AigNumVec.resize(numCloudSets);
			node->pData = new vector<Aig_Obj_t*>(numCloudSets, NULL);

			for(int i = 0; i<numCloudSets; i++) {
				pObj = (*childVec)[i];

				// Create New Cloud
				Aig_Obj_t* cloudObj = Aig_ObjCreateCi(pMan);
				CiCloudIth[i].push_back(Aig_ObjCioId(cloudObj));
				node->AigNumVec[i] = Aig_ObjCioId(cloudObj);
				pObj = Aig_And(pMan, pObj, cloudObj);

				pObj = Aig_ObjCreateCo(pMan, pObj);
				CoIth[i].push_back(Aig_ObjCioId(pObj));

				(*(vector<Aig_Obj_t*>*)node->pData)[i] = pObj;
			}
		}
		else if (Nnf_ObjIsAnd(node) || Nnf_ObjIsOr(node)) {
			vector<Aig_Obj_t*>* childVec0 = (vector<Aig_Obj_t*>*) Nnf_ObjFanin0(node)->pData;
			vector<Aig_Obj_t*>* childVec1 = (vector<Aig_Obj_t*>*) Nnf_ObjFanin1(node)->pData;
			assert(!Nnf_ObjFaninC0(node));
			assert(!Nnf_ObjFaninC1(node));
			assert(childVec0->size() == numCloudSets);
			assert(childVec1->size() == numCloudSets);

			node->AigNumVec.resize(numCloudSets);
			node->pData = new vector<Aig_Obj_t*>(numCloudSets, NULL);

			for(int i = 0; i<numCloudSets; i++) {
				auto child0 = (*childVec0)[i];
				auto child1 = (*childVec1)[i];

				if (Nnf_ObjIsAnd(node))
					pObj = Aig_And(pMan, child0, child1);
				else
					pObj = Aig_Or(pMan, child0, child1);

				// Create New Cloud
				Aig_Obj_t* cloudObj = Aig_ObjCreateCi(pMan);
				CiCloudIth[i].push_back(Aig_ObjCioId(cloudObj));
				node->AigNumVec[i] = Aig_ObjCioId(cloudObj);
				pObj = Aig_And(pMan, pObj, cloudObj);
				(*(vector<Aig_Obj_t*>*)node->pData)[i] = pObj;
			}
		}
		else {
			assert(false);
		}
	}

	for(auto node: _allNodes) {
		delete (vector<Aig_Obj_t*>*)node->pData;
		node->pData = NULL;
	}

	return pMan;
}

void NNf_ObjSetFanin0(Nnf_Obj* parent, Nnf_Obj* child) {
	assert(!Nnf_IsComplement(parent));

	if(Nnf_Regular(child) == NULL)
		child = NULL;

	if(Nnf_ObjChild0(parent) != NULL) {
		// Remove old link
		Nnf_Obj* oldChildReg = Nnf_ObjFanin0(parent);
		bool isOldChildC = Nnf_ObjFaninC0(parent);
		int erased;
		if(isOldChildC) {
			erased = oldChildReg->pFanoutNeg.erase(parent);
		}
		else {
			erased = oldChildReg->pFanoutPos.erase(parent);
		}
		assert(erased == 1);
	}

	parent->pFanin0 = child;

	Nnf_Obj* childReg = Nnf_Regular(child);
	bool isChildC = Nnf_IsComplement(child);
	if(childReg != NULL) {
		set<Nnf_Obj*>& fanoutSet = isChildC?childReg->pFanoutNeg:childReg->pFanoutPos;
		// assert(fanoutSet.count(parent) == 0);
		auto p = fanoutSet.insert(parent);
		assert(p.second);
	}
}

void NNf_ObjSetFanin1(Nnf_Obj* parent, Nnf_Obj* child) {
	assert(!Nnf_IsComplement(parent));

	if(Nnf_Regular(child) == NULL)
		child = NULL;

	if(Nnf_ObjChild1(parent) != NULL) {
		// Remove old link
		Nnf_Obj* oldChildReg = Nnf_ObjFanin1(parent);
		bool isOldChildC = Nnf_ObjFaninC1(parent);
		int erased;
		if(isOldChildC) {
			erased = oldChildReg->pFanoutNeg.erase(parent);
		}
		else {
			erased = oldChildReg->pFanoutPos.erase(parent);
		}
		assert(erased == 1);
	}

	parent->pFanin1 = child;

	Nnf_Obj* childReg = Nnf_Regular(child);
	bool isChildC = Nnf_IsComplement(child);
	if(childReg != NULL) {
		set<Nnf_Obj*>& fanoutSet = isChildC?childReg->pFanoutNeg:childReg->pFanoutPos;
		// assert(fanoutSet.count(parent) == 0);
		auto p = fanoutSet.insert(parent);
		assert(p.second);
	}
}

void Nnf_Man::Nnf_ManDfs_rec(Nnf_Obj * pObj, vector<Nnf_Obj*> &vNodes) {
    if (pObj == NULL)
        return;
    assert(!Nnf_IsComplement(pObj));
    if (Nnf_ObjIsMarkA(pObj))
        return;
    Nnf_ObjSetMarkA(pObj);
    Nnf_ManDfs_rec(Nnf_ObjFanin0(pObj), vNodes);
    Nnf_ManDfs_rec(Nnf_ObjFanin1(pObj), vNodes);
	vNodes.push_back(pObj);
}

// Returns Nodes in Toposorted Order
vector<Nnf_Obj*> Nnf_Man::Nnf_ManDfs() {
    vector<Nnf_Obj*> vNodes;
    Nnf_Obj * pObj;
    int i;

    // Unmark all nodes
    for(auto it: _allNodes)
        Nnf_ObjClearMarkA(it);

    // Add const1 and inputs
    Nnf_ManDfs_rec(const1(), vNodes);
    for(auto it: _inputs_pos)
        Nnf_ManDfs_rec(it, vNodes);
    for(auto it: _inputs_neg)
        Nnf_ManDfs_rec(it, vNodes);

    // collect nodes reachable in the DFS order
    for(auto it: _outputs)
        Nnf_ManDfs_rec(it, vNodes);

    // Unmark all nodes
    for(auto it: _allNodes)
        Nnf_ObjClearMarkA(it);

    if(vNodes.size() != _allNodes.size()) {
	    cout << "NNF: " << endl;
	    this->print();
	    set<Nnf_Obj*> a(_allNodes.begin(), _allNodes.end());
	    set<Nnf_Obj*> v(vNodes.begin(), vNodes.end());

	    vector<Nnf_Obj*> diff;
	    set_difference(a.begin(), a.end(), v.begin(), v.end(),
	        std::inserter(diff, diff.begin()));
	    cout << "Missing Nodes: " << endl;
	    for(auto it:diff) {
	        it->print();
	    }
	    cout << "vNodes.size(): 	" << vNodes.size() << endl;
	    cout << "_allNodes.size(): 	" << _allNodes.size() << endl;
	    // @TODO: necessary for size to be same?
	    assert(vNodes.size() == _allNodes.size());
    }

    return vNodes;
}

void Nnf_Man::Nnf_ManTopoId() {
    vector<Nnf_Obj*> vNodes = Nnf_ManDfs();
    int currId = 0;
    for(auto it: vNodes)
		it->Id = currId++;
    _allNodes = vNodes;
    return;
}

bool Nnf_Man::isWDNNF() {
	vector<int> varsY(this->getCiNum());
	iota(varsY.begin(), varsY.end(), 0);
	return this->isWDNNF(varsY);
}

bool Nnf_Man::isWDNNF(vector<int>& varsY) {
	// Recursive calls

	// Unmark all nodes
	for(auto it: _allNodes) {
	    Nnf_ObjClearMarkA(it);
	    it->pData = NULL;
	}

	// Const1 and Inputs
	this->const1()->pData = new set<int>();
	this->const1()->iData = 1;
	Nnf_ObjSetMarkA(this->const1());
	for (int i = 0; i < this->getCiNum(); ++i) {
		_inputs_pos[i]->pData = new set<int>();
		_inputs_neg[i]->pData = new set<int>();
		_inputs_pos[i]->iData = 1;
		_inputs_neg[i]->iData = 1;
		Nnf_ObjSetMarkA(_inputs_pos[i]);
		Nnf_ObjSetMarkA(_inputs_neg[i]);
	}
	for (auto i:varsY) {
		((set<int>*)(_inputs_pos[i]->pData))->insert(i);
		((set<int>*)(_inputs_neg[i]->pData))->insert(-i);
	}

	assert(_outputs.size() == 1);
	bool result = _outputs.front()->isWDNNF();

	// Unmark all nodes, Free Memory
	for(auto it: _allNodes) {
	    Nnf_ObjClearMarkA(it);
		if(it->pData != NULL) {
			delete (set<int>*) it->pData;
			it->pData = NULL;
		}
	}

	return result;
}

bool Nnf_Obj::isWDNNF() {
	// Recursive calls
	// Store Support in pData as set<int>
	// Store isWDNNF in iData, return

	if(Nnf_ObjIsMarkA(this)) {
		return this->iData == 1;
	}
	Nnf_ObjSetMarkA(this);

	bool res;
	switch(this->Type) {
		case Nnf_Type::NNF_OBJ_NONE:
		case Nnf_Type::NNF_OBJ_CONST1:
		case Nnf_Type::NNF_OBJ_CI_POS:
		case Nnf_Type::NNF_OBJ_CI_NEG:
			assert(false); // Handled Earlier

		case Nnf_Type::NNF_OBJ_CO:
			res = Nnf_ObjFanin0(this)->isWDNNF();
			this->iData = res?1:0;
			// cout << res << " from "; this->print();
			return res;

		case Nnf_Type::NNF_OBJ_OR:
			res = Nnf_ObjFanin0(this)->isWDNNF() and Nnf_ObjFanin1(this)->isWDNNF();
			if(res) {
				set<int>* s0 = (set<int>*) Nnf_ObjFanin0(this)->pData;
				set<int>* s1 = (set<int>*) Nnf_ObjFanin1(this)->pData;
				auto supp = new set<int>();
				set_union (s0->begin(), s0->end(),
							s1->begin(), s1->end(),
							inserter(*supp, supp->begin()));
				this->pData = supp;
			}
			this->iData = res?1:0;
			// cout << res << " from "; this->print();
			return res;

		case Nnf_Type::NNF_OBJ_AND:
			res = Nnf_ObjFanin0(this)->isWDNNF() and Nnf_ObjFanin1(this)->isWDNNF();
			if(res) {
				set<int>* s0 = (set<int>*) Nnf_ObjFanin0(this)->pData;
				set<int>* s1 = (set<int>*) Nnf_ObjFanin1(this)->pData;
				// Check wDNNF violation
				for(auto lit:*s0) {
					if(s1->find(-lit) != s1->end()) {
						res = false;
						break;
					}
				}
				if(!res) {
					cout << "wDNNF violation: ";
					this->print();
					cout << endl;
				}
			}
			if(res) {
				set<int>* s0 = (set<int>*) Nnf_ObjFanin0(this)->pData;
				set<int>* s1 = (set<int>*) Nnf_ObjFanin1(this)->pData;
				auto supp = new set<int>();
				set_union (s0->begin(), s0->end(),
							s1->begin(), s1->end(),
							inserter(*supp, supp->begin()));
				this->pData = supp;
			}
			this->iData = res?1:0;
			// cout << res << " from "; this->print();
			return res;
	}

	// Should not reach here
	assert(false);
}

Nnf_Type SwitchAndOrType(Nnf_Type t) {
	if(t == NNF_OBJ_AND)
		return NNF_OBJ_OR;
	if(t == NNF_OBJ_OR)
		return NNF_OBJ_AND;

	// Wrong Input Type
	assert(false);
}

string type2String(Nnf_Type t) {
	switch(t) {
		case NNF_OBJ_NONE:   return "NNF_OBJ_NONE";
		case NNF_OBJ_CONST1: return "NNF_OBJ_CONST1";
		case NNF_OBJ_CI_POS: return "NNF_OBJ_CI_POS";
		case NNF_OBJ_CI_NEG: return "NNF_OBJ_CI_NEG";
		case NNF_OBJ_CO:     return "NNF_OBJ_CO";
		case NNF_OBJ_AND:    return "NNF_OBJ_AND";
		case NNF_OBJ_OR:     return "NNF_OBJ_OR";
	}
	cerr << "Error: type2String type: " << t << endl;
	assert(false);
}
