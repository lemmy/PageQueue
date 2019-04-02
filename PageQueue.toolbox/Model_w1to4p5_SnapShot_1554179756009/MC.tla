---- MODULE MC ----
EXTENDS PageQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_1554179590763160000 == 
{w1, w2, w3}
----

\* CONSTANT definitions @modelParameterConstants:1Pages
const_1554179590763161000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1554179590763162000 ==
TotalWork
----
=============================================================================
\* Modification History
\* Created Mon Apr 01 21:33:10 PDT 2019 by markus
