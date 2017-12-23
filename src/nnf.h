#include "helper.h"

typedef enum
{
	NNF_OBJ_CONST1,
	NNF_OBJ_CI_POS,
	NNF_OBJ_CI_NEG,
	NNF_OBJ_CO,
	NNF_OBJ_AND,
	NNF_OBJ_OR,
	NNF_OBJ_NONE
} Nnf_Type;

class Nnf_Obj {
public:
	Nnf_Type Type;
	int Id;
	int AIG_num;
	Nnf_Obj* pFanin0;
	Nnf_Obj* pFanin1;
	set<Nnf_Obj*> pFanout;
	int nRefs;

	int iData;
	void* pData;

	Nnf_Obj(int id) : Id(id), Type(NNF_OBJ_VOID) {};
	Nnf_Obj(int id, Nnf_Type t) : Id(id), Type(t) {};
};

class Nnf_Man {
public:
	vector<Nnf_Obj*> inputs_pos;
	vector<Nnf_Obj*> inputs_neg;
	vector<Nnf_Obj*> outputs;
	vector<Nnf_Obj*> allNodes; //(to be stored in order of IDs) (topo-sort)
	Nnf_Obj* pConst1;

	Nnf_Man() {
		this->pConst1 = new Nnf_Obj(0,NNF_OBJ_CONST1);
		allNodes.push_back(this->pConst1);
	}

	~Nnf_Man() {
		for(auto it: allNodes) {
			delete it;
		}
	}
}

// ===========HELPER ROUTINES========
static inline Nnf_Obj *  Nnf_Regular( Nnf_Obj * p )           { return (Nnf_Obj *)((ABC_PTRUINT_T)(p) & ~01);  }
static inline Nnf_Obj *  Nnf_Not( Nnf_Obj * p )               { return (Nnf_Obj *)((ABC_PTRUINT_T)(p) ^  01);  }
static inline Nnf_Obj *  Nnf_NotCond( Nnf_Obj * p, int c )    { return (Nnf_Obj *)((ABC_PTRUINT_T)(p) ^ (c));  }
static inline bool       Nnf_IsComplement( Nnf_Obj * p )      { return (bool)((ABC_PTRUINT_T)(p) & 01);           }

static inline Nnf_Obj *  Nnf_ManConst0( Nnf_Man * p )         { return Nnf_Not(p->pConst1);                      }
static inline Nnf_Obj *  Nnf_ManConst1( Nnf_Man * p )         { return p->pConst1;                               }

static inline Nnf_Obj *  Nnf_ManCi( Nnf_Man * p, int i )      { return (p->vCisi);    }
static inline Nnf_Obj *  Nnf_ManCo( Nnf_Man * p, int i )      { return (Nnf_Obj *)Vec_PtrEntry(p->vCos, i);    }

static inline Nnf_Obj *  Nnf_ManObj( Nnf_Man * p, int i )     { return p->vObjs ? (Nnf_Obj *)Vec_PtrEntry(p->vObjs, i) : NULL;  }

static inline Nnf_Type   Nnf_ObjType( Nnf_Obj * pObj )        { return (Nnf_Type)pObj->Type;       }
static inline int        Nnf_ObjIsNone( Nnf_Obj * pObj )      { return pObj->Type == NNF_OBJ_NONE;   }
static inline int        Nnf_ObjIsConst1( Nnf_Obj * pObj )    { assert(!Nnf_IsComplement(pObj)); return pObj->Type == NNF_OBJ_CONST1; }
static inline int        Nnf_ObjIsCiPos( Nnf_Obj * pObj )     { return pObj->Type == NNF_OBJ_CI_POS;     }
static inline int        Nnf_ObjIsCiNeg( Nnf_Obj * pObj )     { return pObj->Type == NNF_OBJ_CI_NEG;     }
static inline int        Nnf_ObjIsCi( Nnf_Obj * pObj )        { return Nnf_ObjIsCiPos(pObj) or Nnf_ObjIsCiNeg(pObj);     }
static inline int        Nnf_ObjIsCo( Nnf_Obj * pObj )        { return pObj->Type == NNF_OBJ_CO;     }
static inline int        Nnf_ObjIsAnd( Nnf_Obj * pObj )       { return pObj->Type == NNF_OBJ_AND;    }
static inline int        Nnf_ObjIsOr( Nnf_Obj * pObj )        { return pObj->Type == NNF_OBJ_OR;    }
static inline int        Nnf_ObjIsNone( Nnf_Obj * pObj )      { return pObj->Type == NNF_OBJ_NONE;    }
