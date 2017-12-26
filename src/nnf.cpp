#include "nnf.h"

Nnf_Obj::Nnf_Obj(int id) : Id(id), Type(NNF_OBJ_NONE), neg(NULL), pFanin0(NULL), pFanin1(NULL) {};
Nnf_Obj::Nnf_Obj(int id, Nnf_Type t) : Id(id), Type(t), neg(NULL), pFanin0(NULL), pFanin1(NULL) {};

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

Nnf_Man::Nnf_Man() {
	this->pConst1 = createNode(NNF_OBJ_CONST1);
}

Nnf_Man::Nnf_Man(Aig_Man_t* pSrc) : Nnf_Man() {
	cout <<"\n\nInitially" << endl;
	print();

	cout <<"\n\nParsing..." << endl;
	parse_aig(pSrc);

	cout <<"\n\nParsed Aig" << endl;
	print();
	makeNnf();

	cout <<"\n\nPushed Bubbles down" << endl;
	print();
}

Nnf_Man::~Nnf_Man() {
	for(auto it: _allNodes) {
		if(it!=NULL)
			delete it;
	}
}

Nnf_Obj* Nnf_Man::getCiPos(int i) {return _inputs_pos[i];}
Nnf_Obj* Nnf_Man::getCiNeg(int i) {return _inputs_neg[i];}
Nnf_Obj* Nnf_Man::getCo(int i) {return _outputs[i];}
Nnf_Obj* Nnf_Man::getObj(int i) {return _allNodes[i];}
Nnf_Obj* Nnf_Man::const0() {return Nnf_Not(pConst1);}
Nnf_Obj* Nnf_Man::const1() {return pConst1;}

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

void Nnf_Man::orderNodes() {
	vector<Nnf_Obj*> newAllNodes;
	newAllNodes.push_back(pConst1);

	assert(_inputs_neg.size() == _inputs_pos.size());
	int numInputs = _inputs_pos.size();

	for (int i = 0; i < numInputs; ++i) {
		newAllNodes.push_back(_inputs_pos[i]);
		newAllNodes.push_back(_inputs_neg[i]);
	}

	for(auto node: _allNodes) {
		if(!Nnf_ObjIsCi(node)) {
			newAllNodes.push_back(node);
		}
	}

	assert(newAllNodes.size() == _allNodes.size());
	for (int i = 0; i < newAllNodes.size(); ++i) {
		newAllNodes[i]->Id = i;
	}

	_allNodes = newAllNodes;
}

void Nnf_Man::parse_aig(Aig_Man_t* pSrc) {
	int i;
	Aig_Obj_t* pObj, *f0, *f1;

	// Delete Current Nodes
	for (int i = 1; i < _allNodes.size(); ++i) {
		if(_allNodes[i] != NULL)
			delete _allNodes[i];
	}
	_allNodes.resize(1);
	_inputs_pos.clear();
	_inputs_neg.clear();
	_outputs.clear();

	Aig_ManForEachObj( pSrc, pObj, i ) {
		if(Aig_ObjIsConst1(pObj)) {
			pObj->pData = this->pConst1;
		}
		else if(Aig_ObjIsCi(pObj)) {
			pObj->pData = this->createCi();
		}
		else if(Aig_ObjIsCo(pObj)) {
			Nnf_Obj* child = (Nnf_Obj*) Aig_ObjFanin0(pObj)->pData;
			child = Nnf_NotCond(child, Aig_ObjFaninC0(pObj));
			pObj->pData = this->createCo(child);
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

			Nnf_Obj* nObj = this->createNode(NNF_OBJ_AND);
			NNf_ObjSetFanin0(nObj, child0);
			NNf_ObjSetFanin1(nObj, child1);
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

void Nnf_ConeMark_rec(Nnf_Obj * pObj) {
    assert(!Nnf_IsComplement(pObj));
    if(Nnf_ObjIsMarkA(pObj))
        return;
    Nnf_ConeMark_rec(Nnf_ObjFanin0(pObj));
    Nnf_ConeMark_rec(Nnf_ObjFanin1(pObj));
    assert(!Nnf_ObjIsMarkA(pObj)); // loop detection
    Nnf_ObjSetMarkA(pObj);
}

void Nnf_ConeUnmark_rec(Nnf_Obj * pObj) {
    assert(!Nnf_IsComplement(pObj));
    if(!Nnf_ObjIsMarkA(pObj))
        return;
    Nnf_ConeUnmark_rec(Nnf_ObjFanin0(pObj));
    Nnf_ConeUnmark_rec(Nnf_ObjFanin1(pObj));
    assert(Nnf_ObjIsMarkA(pObj)); // loop detection
    Nnf_ObjClearMarkA(pObj);
}

void Nnf_ManDfs_rec(Nnf_Man * p, Nnf_Obj * pObj, vector<Nnf_Obj*> &vNodes) {
    if ( pObj == NULL )
        return;
    assert(!Nnf_IsComplement(pObj));
    Nnf_ManDfs_rec(p, Nnf_ObjFanin0(pObj), vNodes);
    Nnf_ManDfs_rec(p, Nnf_ObjFanin1(pObj), vNodes);
	vNodes.push_back(pObj);
}

vector<Nnf_Obj*> Nnf_ManDfs(Nnf_Man * p) {
    vector<Nnf_Obj*> vNodes;
    Nnf_Obj * pObj;
    int i;

    vNodes.push_back(Nnf_ManConst1(p));
    // collect nodes reachable in the DFS order
    for(auto it: p->_outputs)
        Nnf_ManDfs_rec(p, it, vNodes);
    assert(vNodes.size() == p->_allNodes.size());
    return vNodes;
}

void Nnf_ManTopoId(Nnf_Man * p) {
    vector<Nnf_Obj*> vNodes = Nnf_ManDfs(p);
    int currId = 0;
    for(auto it: vNodes)
		it->Id = currId++;
    p->_allNodes = vNodes;
    return;
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
