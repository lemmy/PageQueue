---- MODULE SimPageQueue ----
EXTENDS PageQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3, w4, w5, w6, w7, w8, w9, w10
----

\* MV CONSTANT definitions Workers
const_162445925788341000 == 
{w1, w2, w3, w4, w5, w6, w7, w8, w9, w10}
----

\* CONSTANT definitions @modelParameterConstants:1Pages
const_162445925788342000 == 
3
----

\* CONSTANT definition @modelParameterDefinitions:3
def_ov_162445925788346000(n, i) ==
TRUE
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_162445925788347000(S) ==
{1,2,3}
----
\* CONSTANT definition @modelParameterDefinitions:6
def_ov_162445925788349000 ==
NoSuspension
----
\* CONSTANT definition @modelParameterDefinitions:7
def_ov_162445925788350000(a, b) ==
FALSE
----
\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_162445925788351000 ==
~Terminating
----
=============================================================================
\* Modification History
\* Created Wed Jun 23 07:40:57 PDT 2021 by markus
