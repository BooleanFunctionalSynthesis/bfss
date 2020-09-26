The Benchmarks are taken from 4 different domains:
a) Arithmetic: These are taken from the arithmetic specifications described in the  paper
Fried, D., Tabajara, L.M., Vardi, M.Y.: BDD-based boolean functional synthesis.
In: CAV (2016). 
The  specifications considered were 
ceiling, floor, intermediate, decomposition, equalization, max, min and subtraction.
For each specification, 6 variants were generated, varying the bit-
width of the arguments of arithmetic operators. We considered bit-widths of 32,
64, 128, 256, 512 and 1024. These benchmarks total 48 in number.

b) Factorization Benchmarks:
These benchmarks correspond  the specification of the integer factorization problem, namely : Z = X *Y and X != 1 and Y !=1.
Here Z, is the input variable and X and Y are the output variables.

We generated benchmarks for different bit-widths
of the product, specifically, for 8, 10, 12, 14, 16 and hence total 5 in number.

c) Disjunctive Decomposition Benchmarks:

The disjunctive decomposition benchmarks were obtained by considering
sequential circuits from the HWMCC10 benchmark suite, and by formulating
the problem of disjunctively decomposing the circuit into components as a
problem of synthesizing Skolem function vectors. Each benchmark is of the
form ∃Y. F (X, Y ), where F (X, Y ) is an arbitrary Boolean formula, and was
generated in the following manner. Some of the larger circuits of the HWMCC10 benchmark suite were chosen
and these benchmarks total 68 in number.

d) QBFEval Benchmarks: These benchmarks were downloaded from the qbflib.org site. The benchmarks belonged to
the 2QBF track of QBFEval 2017 and QBFEval 2018. For CAV2018, the QBFEval benchmarks used belonged to QBFEval 2017. For FMSD, the benchmarks used belong to QBFEval 2018.
  
Generation of Benchmarks:
-------------------------

Arithmetic and Factorization Benchmarks:

For generating the arithmetic and factorization benchmarks, 
we first expressed the problem instance in SMTLIB. We then 
used Boolector-2.1.1 to bit-blast the problem instance and 
express it as an .aig file. 

For example, to generate floor32.aig, we first created floor32.smt 
as follows. 

(benchmark floor32
:logic QF_BV
:extrafuns ((i BitVec[32]))
:extrafuns ((a BitVec[32]))
:extrafuns ((b BitVec[32]))

:formula (or (= (bvmul bv2[32] i) (bvadd a b)) (= (bvadd (bvmul bv2[32] i) bv1[32]) (bvadd a b)) )

; Here we have  ((2i = a+b) \or (2i+1 = a+b)), where a,b are 32-bit input variables and
; i is the 32-bit output variable

)

We then used Boolector as, 

boolector --rewrite-level=0 --rewrite-level-pbr=0 -no-es -no-el -no-ml -no-xl -no-sp  -dam -dai floor32.smt -o floor32.aig 

to bit-blast this and express this in .aig format.



Disjunctive Decomposition Benchmarks:

The disjunctive decomposition benchmarks were obtained as follows:

The HWMCC10 benchmarks are circuits in .aig format. In order to
generate the benchmarks, we first read the circuit, and then extracted the
symbolic transition function of the circuit. Let (x1 = f1 (X, Y )) ∧ . . . ∧
(xn = fn (X, Y )) be the symbolic transition function extracted, where X =
(x1 , . . . , xn ) is the present state, X = (x1 , . . . , xn ) is the next state, Y =
(y1 , . . . , ym ) are the inputs, and f1 , . . . , fn are transition functions for the
state variables x1 , . . . , xn respectively.
The disjunctive decomposition benchmark generated is of the form
∃Y. ((x1 = f1 (X, Y )) ∨ . . . ∨ (xn = fn (X, Y ))). Note that for a given state X,
a value of variables in Y that satisfies the formula (x1 = f1 (X, Y ))∨. . .∨(xn =
fn (X, Y )) gives an outgoing edge from X which is not a self-loop. Hence the
benchmark describes the problem: Synthesize Skolem functions for Y such
that the outgoing edge is not a self-loop.

Conversion of benchmarks in different formats:
----------------------------------------------
.aig/.v to .qdimacs
-------------------

To convert the benchmarks in .aig/.v format to .qdimacs formats, 
we first used the standard Tsietin encoding to derive the CNF. 
The .qdimacs files were generated from the CNF by universally 
quantifying the input variables and existentially quantifying the 
output variables and the Tseitin variables. 

.qdimacs to .aig/.v
-------------------

To convert the .qdimacs to .aig/.v we build an AIG from the .qdimacs file - where each element of a clause is disjuncted using AIG_OR and the conjunction is done with the help of AIG_AND. All the universal and existentially quantified variables are the PIs of the circuit and the existentially quantified varibles are also written to another varstoelim file - so that we know which variables are to be existentially quantified out. In addition, we also  identify clauses for commonly used operators such as  OR, AND, EQUALITY operator and remove the tseitin variables while building the AIG.

Note that these .aig/.v files were used uniformly across all tools which tool .aig/.v as input

conversion for AbsSynthe-Skolem (Directories: aiger_for_abssynthe)
-----------------------------------------------------------------
Since AbsSynthe-Skolem requires the inputs which need to be quantified out to be labelled as controllable inputs, these benchmarks were separately converted to meet the requirements for AbsSynthe-Skolem. 


OrderFiles:
--------
Also note that tools like parSyn and bfss use an order file which gives an order for variable elimination. These order files are in the directory verilog/OrderFiles under each benchmark domain and are listed as benchmarkName_varstoelim.txt.  The heuristic mentioned in the paper has been used to generate these order files. These can also be generated using the genVarOrder executable available with the bfss toolset.


