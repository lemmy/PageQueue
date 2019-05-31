---- MODULE MC ----
EXTENDS PageQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT definitions Workers
const_15593223642446000 == 
{w1, w2, w3}
----

\* SYMMETRY definition
symm_15593223642447000 == 
Permutations(const_15593223642446000)
----

\* CONSTANT definitions @modelParameterConstants:1Pages
const_15593223642448000 == 
3
----

=============================================================================
\* Modification History
\* Created Fri May 31 10:06:04 PDT 2019 by markus
