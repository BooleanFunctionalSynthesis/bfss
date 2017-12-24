#include "nnf.h"

Nnf_Obj::Nnf_Obj(int id) : Id(id), Type(NNF_OBJ_NONE), neg(NULL) {};
Nnf_Obj::Nnf_Obj(int id, Nnf_Type t) : Id(id), Type(t), neg(NULL) {};

Nnf_Man::Nnf_Man() {
	this->pConst1 = new Nnf_Obj(0,NNF_OBJ_CONST1);
	_allNodes.push_back(this->pConst1);
}

Nnf_Man::~Nnf_Man() {
	for(auto it: _allNodes) {
		delete it;
	}
}

Nnf_Obj* Nnf_Man::getCiPos(int i) {return _inputs_pos[i];}
Nnf_Obj* Nnf_Man::getCiNeg(int i) {return _inputs_neg[i];}
Nnf_Obj* Nnf_Man::getCo(int i) {return _outputs[i];}
Nnf_Obj* Nnf_Man::getObj(int i) {return _allNodes[i];}

Nnf_Obj* Nnf_Man::createNode(Nnf_Type t) {
	// assert(t==NNF_OBJ_AND or t==NNF_OBJ_OR);
	int id = _allNodes.size();
	Nnf_Obj* obj = new Nnf_Obj(id, t);
	assert(obj != NULL);
	_allNodes.push_back(obj);
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

Nnf_Obj* Nnf_Man::createCo() {
	Nnf_Obj* co = createNode(NNF_OBJ_CI_POS);
	assert(co != NULL);
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

void parse_aig(Aig_Man_t* pSrc) {
	int i;
	Aig_Obj_t* pObj, *f0, *f1;

	Aig_ManForEachObj( pSrc, pObj, i ) {
		if(Aig_ObjIsConst1(pObj)) {

		}
		else if(Aig_ObjIsCi(pObj)) {

		}
		else {

		}
	}
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
	// Unknown Type
	assert(false); 
}
