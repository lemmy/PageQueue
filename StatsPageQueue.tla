---- MODULE StatsPageQueue ----
EXTENDS SimPageQueue, TLC, TLCExt, CSV, IOUtils, SequencesExt, FiniteSetsExt

CSVTemplateString(columns, delim) ==
    \* Create the Java format string for the values in v: %$1s#%$2s#%$3s#...
    \* We cheat a little by using the fact that TLC normalizes (orders) the input set 1..Len(v).
    FoldSet(LAMBDA a, b: b \o (IF b = "" THEN "%" ELSE delim \o "%") \o ToString(a) \o "$s", "", 1..columns)

------------------------------------------------------------------------------

View ==
    \* pc
    Range(pc)

------------------------------------------------------------------------------

conf == 
    IOEnv.conf

Actions ==
    \* A sequence of all the action names in the spec.
    SetToSeq(DOMAIN TLCGet("stats").behavior.actions)

CSVActionFile == "StatsPageQueue_actions.csv"

ASSUME
    \* Write the header row if the file is empty.
    CSVRecords(CSVActionFile) = 0 =>
        CSVWrite("Mode#View#Trials#Id" \o FoldSeq(LAMBDA a, b: b \o "#" \o a, "", Actions), <<>>, CSVActionFile)

ActionStatisticsStateConstraint ==
    LET values == << TLCGet("config").sched, conf>> 
            \o <<TLCGet("stats").trials, TLCGet("stats").behavior.id>>
            \o [ i \in 1..Len(Actions) |-> TLCGet("stats").behavior.actions[Actions[i]] ]
    IN CSVWrite(CSVTemplateString(Len(values), "#"), values, CSVActionFile)

------------------------------------------------------------------------------

StatisticsStateConstraint ==
    \* Cannot use two or more (state) constraints with TLCDefer because only one would be evalauted.  
    \* Thus, we use a single, outter constraint with TLCDefer that wraps both stats formulas.
    (TLCGet("level") > TLCGet("config").depth) =>
        TLCDefer(
            ActionStatisticsStateConstraint
        )   

=============================================================================
\* Modification History
\* Created Wed Jun 23 07:40:57 PDT 2021 by markus
