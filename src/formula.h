#include "helper.h"

class edge;
class node;
class AigToNNF;

enum node_type
{
	t_AND,
	t_OR,
	t_VAR
};

class node {
public:
	node_type type;
	int var_num;		
	int counter;
	string name;
	node* neg; 			// Duplicated node if not NULL
	bool flipped;
	set<edge> children;
	set<edge> parents;

	node();
	node(node_type t);
	node(node_type t, int v);
	node(node_type t, set<edge>& ch);
	node(node_type t, set<node*>& ch);
	node(string s, node_type t);
	node(string s, node_type t, int v);
	node(string s, node_type t, set<edge>& ch);

	void incCounter(char comp);
	void add_child(edge e);
	void rem_child(edge e);
	void set_children(set<edge>& ch);
	void print();
	void process();
};

class edge {
public:
	node* target;
	bool bubble;

	edge();
	edge(node* trgt);
	edge(bool bubbl);
	edge(bool bubbl, node* trgt);
	bool operator<( const edge& rhs ) const;
	void add_bubble();
	void print();
};

class AigToNNF {
	Abc_Ntk_t *pNtk;
public:
	string pFileName;
	map<string,int>   name2Id;
	map<string,node*> name2Node;
	map<node*,Abc_Obj_t*> node2Obj;
	set<node*> outputs;
	set<node*> inputs;
	static queue<node*> readyNodes;

	AigToNNF(string fname);
	void parse();
	void process();
	void resetCounters();
	void createAig();
	Abc_Ntk_t* getNtk();
	void print();
	int getNumInputs();
};

string type2String(node_type t);
