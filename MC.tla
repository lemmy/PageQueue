---- MODULE MC ----
EXTENDS PageQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
worker1, worker2, worker3
----

\* MV CONSTANT definitions Workers
const_157430886976642000 == 
{worker1, worker2, worker3}
----

\* SYMMETRY definition
symm_157430886976643000 == 
Permutations(const_157430886976642000)
----

\* CONSTANT definitions @modelParameterConstants:1Pages
const_157430886976644000 == 
100
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_157430886976645000 ==
TotalWork
----
=============================================================================
\* Modification History
\* Created Wed Nov 20 20:01:09 PST 2019 by markus
