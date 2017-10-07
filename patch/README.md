# Patches

Dependencies, ABC and UniGen. needs to be patched for BFSS to work. The following are the explanations for the patches. Patches can be found in the directory alongside.

## ABC
ABC does not print binary clauses. To enable printing of binary clauses, we need to set `fUseBinaryClauses` to 0 in the body of procedure `sat_solver_clause_new(sat_solver* s, lit* begin, lit* end, int learnt)` in file `satSolver.c`.

## UniGen
UniGen returns model of just the independent support, we do better and save some computation by returning model of a few more variables. This patch permits UniGen to do just that.
