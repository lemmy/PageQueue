----------------------------- MODULE Schedules -----------------------------
EXTENDS TLC, TLCExt, PageQueue

(*****************************************************************)
(* Remember to add definitions overrides for:                    *)
(* Limit initial states to disk = {1,2,3} with state constraint: *)
(* IF TLCGet("level") = 1 THEN Cardinality(disk) = 3 ELSE TRUE   *)
(* TotalWork <- FALSE                                            *)
(*****************************************************************)

\* ActionConstraint
ScheduleA ==
  LET l  == TLCGet("level")
      w1 == CHOOSE w \in ProcSet: TRUE
      w2 == CHOOSE w \in (ProcSet \ {w1}): TRUE
      \* The desired prefix of a behavior for the workers:
      u  == << \* dequeue page p1 and create a new page p4.
               deq(w2), casA(w2), wt(w2), rd(w2), exp(w2), enq(w2),           
                        claim(w2), clm1(w2), clm2(w2),
               \* dequeue page p2.
               deq(w2), casA(w2), wt(w2), rd(w2), exp(w2), enq(w2),
               \* dequeue page p3 (afterwards, disk is empty).
               deq(w2), casA(w2), wt(w2), rd(w2), exp(w2),
               \* Let w1 execute to wt1.
               deq(w1), casA(w1), enq(w2)
               \* Cannot add Terminating action because of
               \* universal quantification: 
               \* \A self \in ..  
            >>
   IN    \* Always allow wt, wt1, casB, for w1 when possible.
\*      \/ wt1(w1) \/ wt(w1) \/ casB(w1)
      \/ IF l \in DOMAIN u THEN u[l]
         \* Any suffix is admissable when TRUE. To generate a trace when the
         \* end of the prefix has been reached, use Assert(FALSE, "EOB"). To
         \* interactively select successor states at the end of the prefix,
         \* use PickSuccessor(FALSE). Could also fine-tuned to
         \* PickSuccessor(\A w \in ProcSet : pc[w]' # "Violation") or
         \* PickSuccessor(WSafety')
         ELSE Assert(FALSE, "EOB")

=============================================================================
