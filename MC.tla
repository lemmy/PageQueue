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

\* CONSTANT definitions @modelParameterConstants:1Pages
const_157430886976644000 == 
7
----

=============================================================================
\* Modification History
\* Created Wed Nov 20 20:01:09 PST 2019 by markus
