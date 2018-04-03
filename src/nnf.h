#include "helper.h"

typedef enum
{
	NNF_OBJ_NONE,
	NNF_OBJ_CONST1,
	NNF_OBJ_CI_POS,
	NNF_OBJ_CI_NEG,
	NNF_OBJ_CO,
	NNF_OBJ_AND,
	NNF_OBJ_OR
} Nnf_Type;

class Nnf_Obj {
public:
	Nnf_Type Type;
	int Id;
	int AigNum;
	vector<int> AigNumVec;
	int OrigAigId;
	Nnf_Obj* neg;			// Stores negation-node (if available)
	Nnf_Obj* pFanin0;
	Nnf_Obj* pFanin1;
	set<Nnf_Obj*> pFanoutPos;
	set<Nnf_Obj*> pFanoutNeg;

	bool fMarkA;
	int iData;
	void* pData;
	bool isWDNNF();

	Nnf_Obj(int id);
	Nnf_Obj(int id, Nnf_Type t);
	void print();
	int getNumRef();
};

class Nnf_Man {
	string pName;
	vector<Nnf_Obj*> _inputs_pos;
	vector<Nnf_Obj*> _inputs_neg;
	vector<Nnf_Obj*> _outputs;
	vector<Nnf_Obj*> _allNodes; //(to be stored in order of IDs) (topo-sort)
	Nnf_Obj* pConst1;
	map<int,int> _origToNewNodeId;

	void parse_aig(Aig_Man_t* pSrc);
	void makeNnf();
	Aig_Man_t* createAig(bool withCloudInputs);

public:
	Nnf_Man();
	Nnf_Man(Aig_Man_t* pSrc);
	~Nnf_Man();

	// Getters
	Nnf_Obj* getCiPos(int i);
	Nnf_Obj* getCiNeg(int i);
	Nnf_Obj* getCo(int i);
	Nnf_Obj* getObj(int i);
	int      getCiNum();
	int      getCoNum();
	int      getNewAigNodeID(int origAigNodeId);
	Nnf_Obj* createNode(Nnf_Type t);
	Nnf_Obj* createCi();
	Nnf_Obj* createCo(Nnf_Obj* pDriver);
	Nnf_Obj* const0();
	Nnf_Obj* const1();

	// Routines
	bool isWDNNF();
	bool isWDNNF(vector<int>& varsY);
	void pushBubblesDown(Nnf_Obj* nObj);
	void print();
	void Nnf_ManDfs_rec(Nnf_Obj * pObj, vector<Nnf_Obj*> &vNodes);
	vector<Nnf_Obj*> Nnf_ManDfs();
	void Nnf_ManTopoId();
	Aig_Man_t* createAigWithClouds();
	Aig_Man_t* createAigWithoutClouds();
	Aig_Man_t* createAigMultipleClouds(int numCloudSets);
};

// ===========HELPER ROUTINES========
static inline Nnf_Obj *  Nnf_Regular(Nnf_Obj * p)           { return (Nnf_Obj *)((ABC_PTRUINT_T)(p) & ~01);  }
static inline Nnf_Obj *  Nnf_Not(Nnf_Obj * p)               { return (Nnf_Obj *)((ABC_PTRUINT_T)(p) ^  01);  }
static inline Nnf_Obj *  Nnf_NotCond(Nnf_Obj * p, int c)    { return (Nnf_Obj *)((ABC_PTRUINT_T)(p) ^ (c));  }
static inline bool       Nnf_IsComplement(Nnf_Obj * p)      { return (bool)((ABC_PTRUINT_T)(p) & 01);        }

static inline int        Nnf_ObjId(Nnf_Obj * pObj)          { return pObj->Id;                     }
static inline int        Nnf_ObjRefsPos(Nnf_Obj * pObj)     { return pObj->pFanoutPos.size();      }
static inline int        Nnf_ObjRefsNeg(Nnf_Obj * pObj)     { return pObj->pFanoutNeg.size();      }
static inline int        Nnf_ObjRefs(Nnf_Obj * pObj)        { return Nnf_ObjRefsPos(pObj) + Nnf_ObjRefsNeg(pObj);}
static inline Nnf_Type   Nnf_ObjType(Nnf_Obj * pObj)        { return (Nnf_Type)pObj->Type;         }
static inline bool       Nnf_ObjIsNone(Nnf_Obj * pObj)      { return pObj->Type == NNF_OBJ_NONE;   }
static inline bool       Nnf_ObjIsConst1(Nnf_Obj * pObj)    { assert(!Nnf_IsComplement(pObj)); return pObj->Type == NNF_OBJ_CONST1;}
static inline bool       Nnf_ObjIsCiPos(Nnf_Obj * pObj)     { return pObj->Type == NNF_OBJ_CI_POS; }
static inline bool       Nnf_ObjIsCiNeg(Nnf_Obj * pObj)     { return pObj->Type == NNF_OBJ_CI_NEG; }
static inline bool       Nnf_ObjIsCi(Nnf_Obj * pObj)        { return Nnf_ObjIsCiPos(pObj) or Nnf_ObjIsCiNeg(pObj);}
static inline bool       Nnf_ObjIsCo(Nnf_Obj * pObj)        { return pObj->Type == NNF_OBJ_CO;     }
static inline bool       Nnf_ObjIsAnd(Nnf_Obj * pObj)       { return pObj->Type == NNF_OBJ_AND;    }
static inline bool       Nnf_ObjIsOr(Nnf_Obj * pObj)        { return pObj->Type == NNF_OBJ_OR;     }

static inline bool       Nnf_ObjFaninC0(Nnf_Obj * pObj)     { return Nnf_IsComplement(pObj->pFanin0);        }
static inline bool       Nnf_ObjFaninC1(Nnf_Obj * pObj)     { return Nnf_IsComplement(pObj->pFanin1);        }
static inline Nnf_Obj *  Nnf_ObjFanin0(Nnf_Obj * pObj)      { return Nnf_Regular(pObj->pFanin0);             }
static inline Nnf_Obj *  Nnf_ObjFanin1(Nnf_Obj * pObj)      { return Nnf_Regular(pObj->pFanin1);             }
static inline Nnf_Obj *  Nnf_ObjChild0(Nnf_Obj * pObj)      { return pObj->pFanin0;                          }
static inline Nnf_Obj *  Nnf_ObjChild1(Nnf_Obj * pObj)      { return pObj->pFanin1;                          }

static inline bool       Nnf_ObjIsMarkA(Nnf_Obj * pObj)   	{ return pObj->fMarkA;  }
static inline void       Nnf_ObjSetMarkA(Nnf_Obj * pObj)  	{ pObj->fMarkA = true;  }
static inline void       Nnf_ObjClearMarkA(Nnf_Obj * pObj)	{ pObj->fMarkA = false; }

void NNf_ObjSetFanin0(Nnf_Obj* parent, Nnf_Obj* child);
void NNf_ObjSetFanin1(Nnf_Obj* parent, Nnf_Obj* child);

Nnf_Type SwitchAndOrType(Nnf_Type t);
string type2String(Nnf_Type t);
