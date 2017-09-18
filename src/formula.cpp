#include "formula.h"


node::node() : counter(0), neg(NULL), flipped(false) {};
node::node(node_type t) : type(t), neg(NULL), counter(0), flipped(false) {};
node::node(node_type t, int v) : type(t), var_num(v), neg(NULL), counter(0), flipped(false) {};
node::node(node_type t, set<edge>& ch) : type(t), children(ch), neg(NULL), counter(0), flipped(false) {
	for(auto const &e: ch)
		e.target->parents.insert(edge(e.bubble,this));
};
node::node(node_type t, set<node*>& ch) : type(t), neg(NULL), counter(0), flipped(false) {
	for(auto const &it: ch) {
		children.insert(edge(it));
		it->parents.insert(edge(this));
	}
};
node::node(string s, node_type t) : name(s), type(t), neg(NULL), counter(0), flipped(false) {};
node::node(string s, node_type t, int v) : name(s), type(t), var_num(v), neg(NULL), counter(0), flipped(false) {};
node::node(string s, node_type t, set<edge>& ch) : name(s), type(t), children(ch), neg(NULL), counter(0), flipped(false) {
	for(auto const &e: ch)
		e.target->parents.insert(edge(e.bubble,this));
};
void node::incCounter(char comp) {
	counter++;
	if(comp == 'p') {
		assert(counter <= parents.size());
		// cout << name << " counter++";
		if(counter == parents.size()) {
			// cout <<"; Ready!";
			AigToNNF::readyNodes.push(this);
		}
		// cout << endl;
	}
	else if(comp == 'c') {
		assert(counter <= children.size());
		// cout << name << " counter++";
		if(counter == children.size()) {
			// cout <<"; Ready!";
			AigToNNF::readyNodes.push(this);
		}
		// cout << endl;
	}
	else
		assert(false);
}
void node::add_child(edge e) {
	children.insert(e);
	e.target->parents.insert(edge(e.bubble,this));
}
void node::rem_child(edge e) {
	children.erase(e);
	e.target->parents.erase(edge(e.bubble,this));
}
void node::set_children(set<edge>& ch) {
	children = ch;
	for(auto const &e: ch)
		e.target->parents.insert(edge(e.bubble,this));
}
void node::process() { // Duplicate if needed and push bubbles down
	assert(neg == NULL);
	// cout <<"processing "<<name<< endl;

	set<edge> pos_parents;
	set<edge> neg_parents;
	set<edge> new_children;

	for(auto const&it : parents) {
		if(it.bubble)
			neg_parents.insert(it);
		else
			pos_parents.insert(it);
	}

	if(!neg_parents.empty() && pos_parents.empty()) {
		// cout <<"flipping "<<name<< endl;
		flipped = true;
		switch(type) {
			case t_VAR:
				var_num = -var_num;
				break;
			case t_AND:
				type = t_OR;
				break;
			case t_OR:
				type = t_AND;
				break;
			default:
				assert(false);
		}
		for(auto it:neg_parents) {
			it.target->rem_child(edge(it.bubble,this));
			it.target->add_child(edge(!it.bubble,this));
		}
		set<edge> temp = children;
		for(auto it:temp) {
			rem_child(it);
			add_child(edge(!it.bubble,it.target));
		}
	}
	else if(!neg_parents.empty() && !pos_parents.empty()) {
		// cout <<"duplicating "<<name<< endl;
		switch(type) {
			case t_VAR:
				neg = new node("neg_"+name,t_VAR, -var_num);
				assert(children.empty());
				break;
			case t_AND:
				for(auto ch:children)
					new_children.insert(edge(!ch.bubble,ch.target));
				neg = new node(name+"_dup",t_OR, new_children);
				break;
			case t_OR:
				for(auto ch:children)
					new_children.insert(edge(!ch.bubble,ch.target));
				neg = new node(name+"_dup",t_AND, new_children);
				break;
			default:
				assert(false);
		}
		for(auto it:neg_parents) {
			it.target->rem_child(edge(it.bubble,this));
			it.target->add_child(edge(!it.bubble,neg));
		}
	}
	else {
		// cout <<"No Neg Edges..."<< endl;
	}
	for(auto e:children) {
		e.target->incCounter('p');
	}
	if (neg!=NULL) {
		for(auto e:neg->children) {
			e.target->incCounter('p');
		}
	}
}
void node::print() {

	switch(type) {
		case t_AND:
			cout <<name<<"\tn:"<<neg<<"\tf:"<<flipped<<"\t= ";
			cout <<" && (\t";
			for(auto e:children) {
				if(e.bubble)
					cout <<'~';
				cout <<e.target->name<< "\t";
			}
			cout <<")";
			break;
		case t_OR:
			cout <<name<<"\tn:"<<neg<<"\tf:"<<flipped<<"\t= ";
			cout <<" || (\t";
			for(auto e:children) {
				if(e.bubble)
					cout <<'~';
				cout <<e.target->name<< "\t";
			}
			cout <<")";
			break;
		case t_VAR:
			cout <<name<<"\tn:"<<(neg!=0)<<"\tf:"<<flipped<<"\t=(input) ";
	}
	cout << endl;
}

edge::edge() : bubble(false), target(NULL) {};
edge::edge(node* trgt) : bubble(false), target(trgt) {};
edge::edge(bool bubbl) : bubble(bubbl), target(NULL) {};
edge::edge(bool bubbl, node* trgt) : bubble(bubbl), target(trgt) {};
void edge::add_bubble() {
	bubble = !bubble;
}
bool edge::operator<( const edge& rhs ) const {
	return (target<rhs.target) || (target==rhs.target && !bubble && rhs.bubble);
}
void edge::print() {
	cout <<bubble<<" "<<target;
}

queue<node*> AigToNNF::readyNodes = queue<node*>();
AigToNNF::AigToNNF(string fname): pFileName(fname), pAigName(fname), pNtk(NULL), pSrc(NULL) {};
AigToNNF::AigToNNF(Aig_Man_t* pAig): pAigName(string(pAig->pName)), pNtk(NULL), pSrc(pAig) {};

void AigToNNF::parse_verilog() {
	node* tempNode;
	string line;
	vector<string> words;
	bool flag = false;
	bool w_neg;
	int numInputs = 0;
	int numOutputs = 0;

	assert(pFileName != "");

	ifstream file(pFileName);
	while(!flag and getline(file,line)) {
		// cout <<"got line: "<<line<< endl;
		words = tokenize(line, ' ');
		words.back() = words.back().substr(0,words.back().length()-1);
		if(words[0]=="input") {
			numInputs++;
			tempNode = new node(words[1],t_VAR,numInputs);
			inputs.insert(tempNode);
			// cout << "storing " << words[1] << " to " << tempNode << endl;
			name2Node[words[1]] = tempNode;
		}
		else if(words[0]=="output") {
			numOutputs++;
			tempNode = new node(words[1],t_AND);
			outputs.insert(tempNode);
			// cout << "storing " << words[1] << " to " << tempNode << endl;
			name2Node[words[1]] = tempNode;
		}
		else if(words[0]=="wire") {
			tempNode = new node(words[1],t_AND);
			// cout << "storing " << words[1] << " to " << tempNode << endl;
			name2Node[words[1]] = tempNode;
		}
		else if(words[0]=="endmodul") {
			// cout << "endmodule" << endl;
			flag = true;
		}
		else if(words[0]=="module") {
			// cout << "module" << endl;
			pAigName = words[1];
		}
		else if(words[0]=="assign") {
			string tgt = words[1];

			// cout << "accessing " << tgt << endl;
			node* t = name2Node[tgt];
			assert(t!=NULL);

			int iter = 0;
			set<edge> ch;
			for (auto word:words) {
				if(word=="&" || word=="=" || (iter++)<=1)
					continue;
				w_neg = (word[0] == '~');
				if(w_neg)
					word = word.substr(1,string::npos);

				ch.insert(edge(w_neg,name2Node[word]));
				// cout << "accessing " << word << endl;
				assert(name2Node[word]!=NULL);
			}
			// cout << "set_children.. " << endl;
			t->set_children(ch);
			// cout << "set_children! " << endl;
		}
	}
	// cout << "parsed! " << endl;
	return;
}

void AigToNNF::parse_aig() {
	node* nn;
	int numInputs = 0, i;
	Aig_Obj_t* pObj, *f0, *f1;

	Aig_ManForEachObj( pSrc, pObj, i ) {
		if(Aig_ObjIsConst1(pObj)) {
			// IGNORE
			// Have not handled the case of the AIG being a constant
			assert(Aig_ObjRefs(pObj) == 0);
		}
		else if(Aig_ObjIsCi(pObj)) {
			nn = new node(to_string(pObj->Id), t_VAR, ++numInputs);
			inputs.insert(nn);
			name2Node[to_string(pObj->Id)] = nn;
		}
		else {
			nn = new node(to_string(pObj->Id), t_AND);
			name2Node[to_string(pObj->Id)] = nn;

			if(Aig_ObjIsCo(pObj)) {
				outputs.insert(nn);
			}

			set<edge> ch;
			f0 = Aig_ObjFanin0(pObj);
			f1 = Aig_ObjFanin1(pObj);
			if(f0!=NULL)
				ch.insert(edge(Aig_ObjFaninC0(pObj),
							name2Node[to_string(f0->Id)]));

			if(f1!=NULL)
				ch.insert(edge(Aig_ObjFaninC1(pObj),
							name2Node[to_string(f1->Id)]));

			nn->set_children(ch);
		}
	}
}

void AigToNNF::parse() {
	if(pSrc == NULL)
		parse_verilog();
	else
		parse_aig();
}

void AigToNNF::process() {
	for(auto it:outputs)
		AigToNNF::readyNodes.push(it);

	node* curr;
	while(!AigToNNF::readyNodes.empty()) {
		curr = AigToNNF::readyNodes.front();
		AigToNNF::readyNodes.pop();
		curr->process();
	}

	// auto tempSet = inputs;
	// for(auto in:tempSet) {
	// 	if(in->neg != NULL)
	// 		inputs.insert(in->neg);
	// }
}

void AigToNNF::print() {
	cout << "Outputs: " << endl;
	for(auto it:outputs)
		it->print();

	cout << "\nAll: " << endl;
	for(auto it: name2Node) {
		it.second->print();
		if(it.second->neg!=NULL) {
			it.second->neg->print();
		}
	}
}

void AigToNNF::resetCounters() {
	for(auto it: name2Node) {
		it.second->counter = 0;
		if(it.second->neg!=NULL) {
			it.second->neg->counter = 0;
		}
	}
}

void AigToNNF::createAig() {
	Abc_Obj_t* currObj, *lhsObj, *rhsObj;
	node* currNode;
	set<Abc_Obj_t*> badObjects;
	string obName;

	pNtk = Abc_NtkAlloc( ABC_NTK_STRASH, ABC_FUNC_AIG, 1 );
	// pNtk->pName = Extra_UtilStrsav("Aig New");
	Abc_NtkSetName(pNtk,(char*)"Aig New");

	OUT("Resetting counters");
	resetCounters();
	var_num2Id.clear();
	AigToNNF::readyNodes = queue<node*>();
	OUT("pos vars... ");
	for(auto inputNode:inputs) {
		// inputNode->print();
		currNode = inputNode->flipped? inputNode->neg:inputNode;


		currObj = Abc_NtkCreatePi(pNtk);
		assert(currObj!=NULL);
		if(currNode!=NULL) {
			var_num2Id[currNode->var_num] = currObj->Id;
			obName = currNode->name;
			Abc_ObjAssignName(currObj,(char*)obName.c_str(), NULL);
			node2Obj[currNode] = currObj;
			for(auto par_edge:currNode->parents) {
				par_edge.target->incCounter('c');
			}
		}
		else {
			var_num2Id[-inputNode->var_num] = currObj->Id;
			badObjects.insert(currObj);
			obName = inputNode->name;
			Abc_ObjAssignName(currObj,(char*)obName.c_str(), NULL);
		}
	}
	OUT("neg vars... ");
	for(auto inputNode:inputs) {
		// inputNode->print();
		currNode = inputNode->flipped? inputNode:inputNode->neg;

		currObj = Abc_NtkCreatePi(pNtk);
		assert(currObj!=NULL);
		if(currNode!=NULL) {
			var_num2Id[currNode->var_num] = currObj->Id;
			obName = inputNode->flipped?("neg_"+currNode->name):currNode->name;
			Abc_ObjAssignName(currObj,(char*)obName.c_str(), NULL);
			node2Obj[currNode] = currObj;
			for(auto par_edge:currNode->parents) {
				par_edge.target->incCounter('c');
			}
		}
		else {
			var_num2Id[-inputNode->var_num] = currObj->Id;
			badObjects.insert(currObj);
			obName = inputNode->flipped?("neg_"+inputNode->name):inputNode->name;
			Abc_ObjAssignName(currObj,(char*)string("neg_"+inputNode->name).c_str(), NULL);
		}
	}

	// for(auto bo: badObjects) {
	// 	Abc_NtkDeleteObj(bo);
	// }

	while(!AigToNNF::readyNodes.empty()) {
		currNode = AigToNNF::readyNodes.front();
		AigToNNF::readyNodes.pop();
		// cout << "currNode: " << type2String(currNode->type) <<","<< currNode->name << endl;

		auto childEdge = currNode->children.begin();
		lhsObj = node2Obj[childEdge->target];
		assert(lhsObj!=NULL);

		childEdge++;
		if(childEdge != currNode->children.end()) {
			rhsObj = node2Obj[childEdge->target];
			assert(rhsObj!=NULL);
		}
		else {
			switch(currNode->type) {
				case t_AND:
					rhsObj = Abc_AigXor((Abc_Aig_t*)pNtk->pManFunc,
										Abc_AigConst1(pNtk),
										Abc_AigConst1(pNtk));
					// rhsObj = Abc_AigConst1(pNtk);
					break;
				case t_OR:
					rhsObj = Abc_AigConst1(pNtk);
					// rhsObj = Abc_AigXor((Abc_Aig_t*)pNtk->pManFunc,
					// 					Abc_AigConst1(pNtk),
					// 					Abc_AigConst1(pNtk));
					break;
				default:
					assert(false);
			}
		}
		// cout << "currNode type: " << type2String(currNode->type) << endl;

		switch(currNode->type) {
			case t_AND:
				currObj = Abc_AigOr((Abc_Aig_t*)pNtk->pManFunc,lhsObj,rhsObj);
				// currObj = Abc_AigAnd((Abc_Aig_t*)pNtk->pManFunc,lhsObj,rhsObj);
				break;
			case t_OR:
				currObj = Abc_AigAnd((Abc_Aig_t*)pNtk->pManFunc,lhsObj,rhsObj);
				// currObj = Abc_AigOr((Abc_Aig_t*)pNtk->pManFunc,lhsObj,rhsObj);
				break;
			default:
				assert(false);
		}
		node2Obj[currNode] = currObj;

		for(auto e:currNode->parents) {
			e.target->incCounter('c');
		}
	}
	// cout << "Processed" << endl;
	// cout << "pNtk: " <<pNtk<< endl;

	for(auto currOutNode:outputs) {
		currObj = Abc_NtkCreatePo(pNtk);
		// cout << "currObj: " <<currObj<< endl;
		assert(node2Obj[currOutNode]!=NULL);
		Abc_ObjAddFanin(currObj,node2Obj[currOutNode]);
		// cout << "added fanin" << endl;
	}
	// cout << "returning.." << endl;
}

Abc_Ntk_t* AigToNNF::getNtk() {
	if(pNtk == NULL) {
		createAig();
		// swapAndOr();
	}

	return pNtk;
}

// void swapAndOr() {
// 	assert(pNtk != NULL);

// }

int AigToNNF::getNumInputs() {
	return inputs.size();
}


string type2String(node_type t) {
	switch(t) {
		case t_AND: return "t_AND";
		case t_OR: return "t_OR";
		case t_VAR: return "t_VAR";
	}
}
