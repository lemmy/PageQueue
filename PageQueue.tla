- Variant A: Simulate fixed-length traces and see how (page) throughput
  changes over varying numbers of workers.  Input results into USL. This
  is exactly how it would work with the implementation.

- Variant B1: Count contention & coherence at a per-behavior level by adding
  auxiliary variables to the spec. Generate behaviors with simulation.
  
- Variant B2: No spec variables but TLCSet/TLCGet

- Variant C: Basic/Aggregating hyperproperties maintained with TLCSet/TLCGet.

- Needs: Disable suspension because this functionality is not relevant for
  scalability (see `NoSuspension` definition below).

- Features of implementation not modelled in spec:
  -- Size of a pages
  -- Function that dynamically determines page size
  -- blocking time of disk reads and writes
  -- Coherence/cross-chatter due to CAS
  
Why is there no speed-up with more workers at the spec level?
a) Approach of predicting scalability at the spec level, ultimately, doesn't work
b) Algorithm, ultimately, doesn't scale
c) Markus has made a stupid mistake


----------------------------- MODULE PageQueue -----------------------------
EXTENDS Integers, Sequences, SequencesExt, Functions, FiniteSets, TLC, TLCExt,
        Randomization

(***********************************************)
(* The set of naturals without zero: 1,2,3,... *)
(***********************************************)
NatP == Nat \ {0}

(*******************************************************************)
(* The largest element in the given sequence assuming the elements *)
(* have an order.                                                  *) 
(*******************************************************************)
Max(S) == CHOOSE s \in S : \A e \in S : s >= e

(*******************************************************************)
(* seq is assumed to be a sequence of functions. Equals a sequence *)
(* where each element is the i-th element of the nested functions. *)
(*******************************************************************)
Reduce(seq, i) == [ idx \in 1..Len(seq) |-> seq[idx][i] ]

(*******************************************************************)
(* A record representing a logical queue operation                 *)
(*******************************************************************)
Op(o, p) == [ oper |-> o, page |-> p ]

-----------------------------------------------------------------------------

CONSTANT Workers,
         (* Maximum number of pages to write *)
         (* unless a violation is detected.  *)
         Pages                
                              
ASSUME /\ Workers # {}            (* At least one worker. *)
       /\ Pages \in NatP

-----------------------------------------------------------------------------

\* Note: To collect statistics with simulation, in the model do:
\* - redefine:
\* -- appendHistory to <<>>
\* -- TotalWork to FALSE
\* - Prevent a suffix of infinite stuttering to keep simulation from
\* -- Action Constraint: ~Terminating
\*   generating a suffix of stuttering steps up to -depth N. 
\* - Increase -depth to a large value 
\* - Amend behavior spec to initialize TLCSet registers:
\* -- InitializeStats /\ Spec
\* - Add PrintStats as Post Condition on TLC Options page of model
\* - Re-define SetOfRandomElement and SetOfInitialDisks in model (see below)

SetOfRandomElement(S) == 
   S \* Redefine to {RandomElement(S)} in model for simulation. 
     \* {RandomElement(S)} \ {{1}} to reduce the probability of a violation to zero.

SetOfInitialDisks == { 1..i : i \in 1..Pages } \* Redefine to {{1}} in model for sim.

(****************************************************************************)
(* The (first) argument of TLCSet/Get has to be in Nat.  Thus, map the set  *)
(* of workers to the subset 1..Cardinality(Workers) of Nat.  We do not care *)
(* what the actual mapping is and thus choose one of it.                    *)
(* In idiomatic TLA+ this would be expressed as:                            *) 
(*   CHOOSE mapping \in [ Workers -> 1..Cardinality(Workers) ]: TRUE        *)
(* however, this becomes a bottleneck for TLC for larger Workers set.       *)
(****************************************************************************)
w2i == CHOOSE mapping \in RandomSubset(Cardinality(Workers),
                               [ Workers -> 1..Cardinality(Workers) ]): TRUE

(****************************************************************************)
(* Initialize the register of TLCSet for all values in the range of w2i.    *)
(* Amend model's behavior spec to: InitializeStats /\ Spec                  *)
(****************************************************************************)
ASSUME Cardinality(Workers) < 20
InitializeStats ==
   \* Registers 20..22 to keep statistics about the branches related to
   \* livelock detection & resolution/recovery.
   \A n \in (20..22): TLCSet(n, [ i \in 1..Pages+20 |-> 0 ])

(****************************************************************************)
(* Print the value of all registers/for all values in the range of w2i.     *)
(* Should be evaluated as a POSTCONDITION in the model's config file.       *)
(****************************************************************************)
PrintStats == 
     /\ \A n \in 20..22 : PrintT(<<n, TLCGet(n)>>)

(****************************************************************************)
(* For the given worker, increment the register by one. TLCDefer makes sure *)
(* that we don't inflate the statistics by incrementing the register for    *)
(* states that are not part of the current behavior.  This is only relevant *)
(* In simulation mode s.t. the expression e in TLCDefer(e) will be          *)
(* evaluated only for the states of the current and not for the set of all  *)
(* states of the behavior and their successors.  For exhaustive model-      *)
(* checking, a model override should turn IncrementStats into a no-op by    *)
(* substituting TRUE for it.                                                *)
(* Get TLCDefer by downloading the TLA+ CommunityModules.jar from           *)
(* http://modules.tlapl.us/ and adding it to TLC's classpath.               *)
(****************************************************************************)
\* IncrementStats could be defined as a CONSTANT operator and this def be moved elsewhere. 
IncrementStats(n, i) == 
    TLCDefer(
         TLCSet(n, [ TLCGet(n) EXCEPT ![i] = @ + 1 ]))

-----------------------------------------------------------------------------

(******************************************************************)
(* Hint: Separation into Finish and Violation not needed by the   *)
(* implementation. The implementation just returns null. Instead, *)
(* only the spec uses it to be able to state stronger invariants. *)
(******************************************************************)
fin == CHOOSE fin : fin \notin Nat
vio == CHOOSE vio : vio \notin Nat \cup {fin}
np  == CHOOSE np  : np  \notin Nat \cup {fin,vio}
sus == CHOOSE sus : sus \notin Nat \cup {fin,vio,np}

----------------------------------------------------------------------------

(***************************************************************************
--algorithm PageQueue {
       variables 
         (*********************************************************************)
         (* A strictly monotone increasing counter. Its value marks the       *)
         (* last page that has been enqueued.  Iff its value is negativ,      *)
         (* it serves as a signal for consumers/workers (compare fin and      *)
         (* vio). Initially, no page has been dequeued.                       *)
         (*********************************************************************)
         tail = 0;
         (*********************************************************************)
         (* The pages that have been written to disk during the generation of *)
         (* the initial states. disk \in  { {1}, {1,2}, {1,2,3}, ... }        *)
         (*********************************************************************)
         disk \in SetOfInitialDisks;
         (*********************************************************************)
         (* A strictly monotone increasing counter. Its value marks the last  *)
         (* page that has been enqueued.                                      *)
         (*********************************************************************)
         head = Max(disk);
         (*********************************************************************)
         (* Auxiliary/History variable to check properties. Initialized to    *)
         (* match disk.                                                       *)
         (*********************************************************************)
         enqHistory = 1..Cardinality(disk);
         deqHistory = {};
       
       define {
           (*****************************************************************)
           (* Make state space explicitly finite (see enq) instead of       *)
           (* with a state constraint that interfers with liveness checking.*)
           (*****************************************************************)
           \* A history-independent definition of TotalWork that gives only a
           \* bound for tail but not head does not make the state space finite.
           \* Unsurprisingly, it allows behaviors that keep increasing head,
           \* which semantically corresponds to exploring a set of states that
           \* have infinite successor states.
           TotalWork(h,t) == h > Pages
       
           (******************************)
           (* Type correctness invariant *)
           (******************************)
           TypeOK == 
                 /\ tail \in (Nat \cup {fin,vio,sus})
                 /\ head \in NatP
                 /\ disk \subseteq NatP
\*                 /\ t \in (Nat \cup {fin,vio})
\*                 /\ h \in (NatP \cup {np})
       
           (********************************************************************)
           (* Safety Property:                                                 *)
           (* There are never duplicates in history nor disk. Upon termination *)
           (* all work is either done or a violation has been found.           *)
           (********************************************************************)
           WSafety == 
                   (*************************************************************)
                   (* After termination a worker either found a violation (vio) *)
                   (* or a worker signalied finish (fin) in which case all      *)
                   (* scheduled work is done (disk = {}).                       *)
                   (*************************************************************)
                   /\ (\A p \in Workers : pc[p] = "Done") => 
                       \/ tail = vio
                       \/ /\ tail = fin
                          /\ disk = {}
                          (************************************************************)
                          (* Any enq'ed page has also been deq'ed.                    *)
                          (************************************************************)
                          /\ enqHistory = deqHistory
       }
       
       macro Read(disk, page) {
          disk := disk \ {page};
          
          \* correctness/history
\*          assert page \notin deqHistory;
\*          deqHistory := deqHistory \cup {page};
       }
       macro Write(disk,page) {
          disk := disk \cup {page};
          
          \* correctness/history
\*          assert page \notin enqHistory;
\*          enqHistory := enqHistory \cup {page};
       }
       
       (*******************************************************)
       (* Atomicity is implicit due to the absence of labels. *)      
       (*******************************************************)
       macro CAS(result, var, expected, new) {
           if (var = expected) {
               var := new;
               result := TRUE
           } else { 
               result := FALSE
           }
       }


       fair process (ProcName = "main") 
            variables
                  \* terminated and condition could, perhaps, both be merged into
                  \* phaser and special (negative) values be used to represent
                  \* terminated and condition.  This is outside the scope of this
                  \* spec because an implementation will use a java.concurrent.Phaser.
                  (* Signal set by workers if all work is done or a violation    *)
                  (* has been found.                                             *)
                  terminated = FALSE;
                  (* Counts the number of arrived parties at the phaser.         *)
                  (* suspension/main awaits phaser = Cardinality(Workers)        *)
                  phaser = 0;
                  (* Signal set by suspension/main to release workers after main *)
                  (* has completed its work.                                     *)
                  condition = FALSE;
                  (* 1) Handle ABA problem of updating tail.                     *)
                  (* 2) Hack discussed in comment about await tail # tmp below.  *)
                  tmp = tail; {
            m0:  while (~terminated) {
                     m1: (* await tail # tmp rules out behaviors that indefinitely suspend *)
                         (* all workers without workers ever making (global) progress,     *)
                         (* which violates the liveness property Termination.              *)
                         (* An alternative would, perhaps, be to state an involed fairness *)
                         (* property for m1 that enables the action when tail changes.     *)
                         (* However, that would leave m1 disabled even after all workers   *)
                         (* have terminated causing suspension to stutter indefinitely.    *)
                         (* In other words, we would have to come up with a fairness       *)
                         (* constraint that takes the value of the worker's pc variables   *)
                         (* into account, which would result in a non-machine closed spec. *)
                         (* The whole issue is more or less theoretical anyway.  An        *)
                         (* implementation will suspend based on a periodic timer that -   *)
                         (* by default - is set to make it highly unlikely that workers    *)
                         (* won't make any progress.  Termination of suspension is         *)
                         (* guaranteed by the runtime iff suspension/main is configured to *)
                         (* be a daemon thread.                                            *)  
                         await tail # tmp;
                         await phaser = 0;
                         condition := FALSE;
                         tmp := tail;
                         if (tmp = vio \/ tmp = fin) {
                             tail := tmp;
                             goto Done;
                         };
                         (* CAS tail to SUSPEND and remember old value *)
                     m2: \* "Inline" CAS to get away without an extra result variable for this process.
                         if (tail = tmp) {
                             tail := sus;
                             goto m3;
                         } else {
                             goto m0;
                         };
                         (* Phaser#awaitAnd... called in this/main thread. *)
                     m3: await phaser = Cardinality(Workers) \/ terminated;
                         if (terminated) {
                            condition := TRUE;
                            goto Done;
                         };
                         (* Do main thread things and set tail back to t. *)
                     m4: skip;
                         (* See comment about await tail # tmp above. *)
                         tail := tmp;
                         (* Resume workers. *)
                         (* Phaser#arriveAndAwaitAdvance *)
                     m5: condition := TRUE;
            };
       }
       
       (******************************************************************)
       (* A worker process has the following high-level stages:          *)
       (* 1) deq to rd:  Dequeue a page iff one is available.            *)
       (* 2) exp:        Evaluate the next-state relation.               *)
       (* 3) enq to wrt: Enqueue a newly generated page.                 *)
       (* In the first stage a worker will check for a "fin" or "vio"    *)
       (* signal from another worker.                                    *)
       (******************************************************************)
       fair process (worker \in Workers)
            \* h doesn't suffer from the ABA problem because it is monotonically
            \* increasing. t, on the other hand, can exhibit ABA because its
            \* value increments *and* decrements (to vio or fin) shortly before
            \* termination. 
            variables result = FALSE, t = 0, h = np; {
            
            (****************************************************************)
            (* 1. Stage: Dequeue an unexplored page iff one is available.   *)
            (****************************************************************)
            deq: t := tail;
                 if (t = vio) {
                   goto Done;
                 } else if (t = fin) {
                   assert disk = {};
                   goto Done;
                 } else if (t = sus) {
                     suspendedA: phaser := phaser + 1;
                     suspendedB: await condition \/ terminated;
                                 phaser := phaser - 1;
                     goto deq;
                 } else {
                   casA: CAS(result, tail, t, t + 1);
                         if (result) {
                            (******************************************************)
                            (* Set (local) t to value CASed iff CAS successful.   *)
                            (* Translates to Java's AtomicInteger#incrementAndGet *)
                            (******************************************************)
                            t := t + 1;
                            goto wt;
                         } else {
                            (***********************************)
                            (* CAS can fail for two reasons:   *)
                            (*  a) Another worker dequeued the *)
                            (*     page (normal case).         *)
                            (*  b) Model checking finished     *)
                            (*  In both cases return to deq.   *)
                            (***********************************)
                            goto deq;
                         };
                 };

            (***************************************************************)
            (* Spin until a page is available and can be read. In case all *)
            (* other workers spin here too, the workers will eventually    *)
            (* terminate once one of the worker CASes "fin".               *)
            (***************************************************************)
            wt: while (t \notin disk) {
            wt1:   if (tail = vio) {
                       goto Done;
                    } else if (tail = fin) {
                       assert h = np /\ disk = {};
                       goto Done;
                    } else if (tail = sus) {
                       suspendedA1: phaser := phaser + 1;
                       suspendedB1: await condition \/ terminated;
                                    phaser := phaser - 1;
                       goto wt;
                    } else if (head = tail - Cardinality(Workers)) {
                       (*******************************************************)
                       (* This branch guarantees termination after all states *)
                       (* have been explored.                                 *)
                       (* ----------------------------------------------------*)
                       (* The current worker (self) detected the termination  *)
                       (* condition and signals "fin" to the other workers.   *)
                       (* ----------------------------------------------------*)
                       (*TODO: LazySet is probably good enough because an     *)
                       (*      unsuccessful CAS means another worker CAS'ed   *)
                       (*      fin before us (in which case we can go to      *)
                       (*      Done). This optimization is more about elegance*)
                       (*      than about performance though.                 *)
                       (*******************************************************)
                       assert h = np;
                       casB: CAS(result, tail, t, fin);
                             if (result) {
                                assert disk = {};
                                terminated := TRUE;
                                goto Done;
                             } else {
                                (************************************************)
                                (* Failed to signal termination because another *)
                                (* worker signaled termination first.           *)
                                (************************************************)
                                goto wt;
                             }
                    } else if (h # np /\ h = t) {
                        \* 1. optimization:
                        \* Trivial live-lock of one worker with itself.
                        await IncrementStats(20, h);
                        Write(disk, h);
                        h := np;
                        goto wt;
                    } else if (h # np /\ h > t) {
                        \* 2. optimization:
                        \* Break a (cyclic) live-lock of 2..n workers by making
                        \* those workers - that are part of the cycle - release
                        \* when they wait on a page that is newer than their
                        \* current page.  In other words, the workers waiting
                        \* for older pages do *not* release/return their pages.
                        await IncrementStats(21, h);
                        Write(disk, h);
                        h := np;
                        goto wt;
                    } else if (h # np /\ h < t /\ head <= tail) {
                        \* Stop waiting for a page that may never exist (it might
                        \* only exist as a result of this very enqueue operation).
                        \* In other words, this branch is taken when a worker
                        \* has not been able to fill its current page h and, thus,
                        \* has to request another page (but there are none left).
                        \* An implementation may collapsed the two branches above
                        \* into this one, provided the 'h < t' conjunct is dropped
                        \* from this conditional.
                        (**********************************************************)
                        (* A page transitions through the following states:       *)
                        (* New > Written > Claimed > Read > Deleted               *)
                        (* The interesting transition is from New to Written.     *)
                        (* The existance of a new page is known to the set of     *)
                        (* workers because head has been increased.  However,     *)
                        (* no worker can claim this page until it is written      *)
                        (* to storage (e.g. the file-system). A new page gets     *)
                        (* written when it is full, unless it cannot be filled    *)
                        (* completely because workers run out of unexplored       *)
                        (* states to generate successor states. This is where     *)
                        (* a worker writes an underfull page to storage (disk).   *)
                        (* -----------------------------------------------------  *)
                        (* This branch prevents premature termination before all  *)
                        (* states have been explored. Why is it guaranteed that   *)
                        (* worker_i, that holds a new page, arrives here before   *)
                        (* another worker observes tail = head + Car(W) above?    *)
                        (* For Car(W) = 1, it is easy to see that the (only)      *)
                        (* worker first arrives here.                             *)
                        (* -----------------------------------------------------  *)
                        (* Approximates FIFO ordering because worker_i whose t_i  *)
                        (* is greater than t_j of worker_j may consume page t_i   *)
                        (* before t_j. This is however a general property of this *)
                        (* queue, hence relaxed queue.                            *)
                        (**********************************************************)
                        await IncrementStats(22, h);
                        Write(disk, h);
                        h := np;
                        goto wt;
                    } else {
                        (***************************************************)
                        (* Page not yet readable (the producer of the page *)
                        (* has not yet written the page to disk).          *) 
                        (***************************************************)
                        skip; \* Same as goto wt;
                    }
                 };
            rd:  assert t \in disk;
                 Read(disk, t);
                 
            (*****************************************************************)
            (* 2. Stage:  Evaluate spec's next-state relation.               *)
            (*                                                               *)
            (* It's not worth to merge this state into enq to reduce states. *)
            (*                                                               *)
            (* Bound spec to a finite state space.  Using a state constraint *)
            (* such as Len(history) < Pages is more elegant but causes       *)
            (* trouble when checking liveness because the property can be    *)
            (* vacuously true (see Specifying Systems section 13.4.5).       *)
            (*****************************************************************)
            exp: if (TotalWork(head, tail)) {
                     goto deq;
                 } else {
                     goto enq;
                 };
            
           (****************************************************************)
           (* 3. Stage: Append successor states to an existing page        *)
           (* (h # -1) or create a new one.                                *)
           (*                    h = np (new)        |  h # np (existing)  *)
           (*                  ----------------------|---------------      *)
           (*  violation:       CAS(fin),goto Done   | CAS(fin), goto Done *)
           (*  no succ:         (claim,) goto deq    | goto deq            *)
           (*  fits into page:  claim, goto deq      | goto deq            *)
           (*  exactly fits p:  claim, wrt, goto deq | wrt, goto deq       *)
           (*  exceeds page:    claim, wrt, goto enq | wrt, goto enq       *)
           (*                                                              *)
           (*  ("goto enq" means we have to end up claiming a new page!!!) *)
           (****************************************************************)
            enq: if (h = np) {
                      \* Contrary to explicit sets, TLC will treat an interval
                      \* lazily and not enumerate it to draw a RandomElement.
                      with ( i \in SetOfRandomElement(1..50) ) {
                        either { await i \in 1..1;  goto violation; } 
                            (* Set of successor states is not empty, create *)
                            (* a new page for them.                         *)
                            or { await i \in 2..50; goto claim; };
                            (* For symmetry with the else branch, one would *)
                            (* expect a goto deq here. However, we claim    *)
                            (* a page anyway (a worker can goto deq from    *)
                            (* claim). Not claiming a page would violate    *)
                            (* the WSafety property, because of premature   *)
                            (* termination (head would be lower than        *)
                            (* expected.  Actual termination is detected by *)
                            (* N claimed pages where N equals               *)
                            (* Cardinality(Workers).                        *)
                      }
\*                        either { goto violation; } 
\*                            or { goto claim; };
                 } else if (h # np) {
                      with ( i \in SetOfRandomElement(1..50) ) {
                         either { await i \in 1..1;   goto violation; }
                             (* Set of successor states is empty (no succ). *)
                             (* (Can lead to temporary livelock that have   *)
                             (* to be and are resolved in wt1 above)        *)
                             or { await i \in 2..2; goto deq; };
                             (* Current page is full, thus write it to disk *) 
                             or { await i \in 3..50;  goto wrt; } 
                      }
\*                         either { goto violation; } 
\*                             or { goto wrt; } 
\*                             or { goto deq; };
                 };

            claim: assert h = np;
                   head := head + 1;
                   h := head;
                   with ( i \in SetOfRandomElement(2..3) ) {
                     (* set of successor states fits into    *)
                     (* page, thus no need to write page.    *)
                     (* Just get the next page of unexplored *)
                     (* states.                              *)
                     (* (Can lead to temporary livelock that *)
                     (* have to be and are resolved in wt1   *)
                     (* above!)                              *) 
                     either { await i \in 2..2; goto deq; } 
                     (* set of successor states does not fit *)
                     (* into page, thus write it.            *)
                         or { await i \in 3..3; goto wrt; };
                   };
\*                                 either { goto deq; } 
\*                                     or { goto wrt; };
            
            (*************************************************************)
            (* Write page to disk. Intuitively, one would write the page *)
            (* first (wrt) before enqueueing it (enq). However, enq      *)
            (* determines the identifier (e.g. file-name) of the page.   *)
            (*************************************************************)
            wrt: Write(disk, h);
                 h := np;
                 with ( i \in SetOfRandomElement(2..3) ) {
                      (* With the current page written and done, either  *)
                      (* go to dequeue a new page or explore additional  *)
                      (* states. The latter models the case where the    *)
                      (* set of successor states doesn't fit into a      *)
                      (* single page.                                    *)
                      (* (deq can lead to temporary livelock that have   *)
                      (* to be and are resolved in wt1 above)            *)
                      either { await i \in 2..2; goto deq; } 
                          or { await i \in 3..3; goto exp; };
                 };
\*                      either { goto deq; } 
\*                          or { goto exp; };
                     
            \*-----------------------------------------------------------*\
            
            (*************************************************************)
            (* Violation Stage                                           *)
            (*                                                           *)
            (* TODO:                                                     *)
            (* The implementation will have already claimed a page (the  *) 
            (* goto violation above in enq doesn't really reflect this). *)
            (*************************************************************)
            violation: CAS(result, tail, t, vio);
                       if (result) {
                             terminated := TRUE;
                             goto Done;
                       } else {
                             retry: t := tail;
                             goto violation;
                       };           
       }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "a2c119de" /\ chksum(tla) = "c5260d2c")
VARIABLES tail, disk, head, enqHistory, deqHistory, pc

(* define statement *)
TotalWork(h,t) == h > Pages




TypeOK ==
      /\ tail \in (Nat \cup {fin,vio,sus})
      /\ head \in NatP
      /\ disk \subseteq NatP








WSafety ==





        /\ (\A p \in Workers : pc[p] = "Done") =>
            \/ tail = vio
            \/ /\ tail = fin
               /\ disk = {}



               /\ enqHistory = deqHistory

VARIABLES terminated, phaser, condition, tmp, result, t, h

vars == << tail, disk, head, enqHistory, deqHistory, pc, terminated, phaser, 
           condition, tmp, result, t, h >>

ProcSet == {"main"} \cup (Workers)

Init == (* Global variables *)
        /\ tail = 0
        /\ disk \in SetOfInitialDisks
        /\ head = Max(disk)
        /\ enqHistory = 1..Cardinality(disk)
        /\ deqHistory = {}
        (* Process ProcName *)
        /\ terminated = FALSE
        /\ phaser = 0
        /\ condition = FALSE
        /\ tmp = tail
        (* Process worker *)
        /\ result = [self \in Workers |-> FALSE]
        /\ t = [self \in Workers |-> 0]
        /\ h = [self \in Workers |-> np]
        /\ pc = [self \in ProcSet |-> CASE self = "main" -> "m0"
                                        [] self \in Workers -> "deq"]

m0 == /\ pc["main"] = "m0"
      /\ IF ~terminated
            THEN /\ pc' = [pc EXCEPT !["main"] = "m1"]
            ELSE /\ pc' = [pc EXCEPT !["main"] = "Done"]
      /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, terminated, 
                      phaser, condition, tmp, result, t, h >>

m1 == /\ pc["main"] = "m1"
      /\ tail # tmp
      /\ phaser = 0
      /\ condition' = FALSE
      /\ tmp' = tail
      /\ IF tmp' = vio \/ tmp' = fin
            THEN /\ tail' = tmp'
                 /\ pc' = [pc EXCEPT !["main"] = "Done"]
            ELSE /\ pc' = [pc EXCEPT !["main"] = "m2"]
                 /\ tail' = tail
      /\ UNCHANGED << disk, head, enqHistory, deqHistory, terminated, phaser, 
                      result, t, h >>

m2 == /\ pc["main"] = "m2"
      /\ IF tail = tmp
            THEN /\ tail' = sus
                 /\ pc' = [pc EXCEPT !["main"] = "m3"]
            ELSE /\ pc' = [pc EXCEPT !["main"] = "m0"]
                 /\ tail' = tail
      /\ UNCHANGED << disk, head, enqHistory, deqHistory, terminated, phaser, 
                      condition, tmp, result, t, h >>

m3 == /\ pc["main"] = "m3"
      /\ phaser = Cardinality(Workers) \/ terminated
      /\ IF terminated
            THEN /\ condition' = TRUE
                 /\ pc' = [pc EXCEPT !["main"] = "Done"]
            ELSE /\ pc' = [pc EXCEPT !["main"] = "m4"]
                 /\ UNCHANGED condition
      /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, terminated, 
                      phaser, tmp, result, t, h >>

m4 == /\ pc["main"] = "m4"
      /\ TRUE
      /\ tail' = tmp
      /\ pc' = [pc EXCEPT !["main"] = "m5"]
      /\ UNCHANGED << disk, head, enqHistory, deqHistory, terminated, phaser, 
                      condition, tmp, result, t, h >>

m5 == /\ pc["main"] = "m5"
      /\ condition' = TRUE
      /\ pc' = [pc EXCEPT !["main"] = "m0"]
      /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, terminated, 
                      phaser, tmp, result, t, h >>

ProcName == m0 \/ m1 \/ m2 \/ m3 \/ m4 \/ m5

deq(self) == /\ pc[self] = "deq"
             /\ t' = [t EXCEPT ![self] = tail]
             /\ IF t'[self] = vio
                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                   ELSE /\ IF t'[self] = fin
                              THEN /\ Assert(disk = {}, 
                                             "Failure of assertion at line 330, column 20.")
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                              ELSE /\ IF t'[self] = sus
                                         THEN /\ pc' = [pc EXCEPT ![self] = "suspendedA"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "casA"]
             /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, 
                             terminated, phaser, condition, tmp, result, h >>

suspendedA(self) == /\ pc[self] = "suspendedA"
                    /\ phaser' = phaser + 1
                    /\ pc' = [pc EXCEPT ![self] = "suspendedB"]
                    /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, 
                                    terminated, condition, tmp, result, t, h >>

suspendedB(self) == /\ pc[self] = "suspendedB"
                    /\ condition \/ terminated
                    /\ phaser' = phaser - 1
                    /\ pc' = [pc EXCEPT ![self] = "deq"]
                    /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, 
                                    terminated, condition, tmp, result, t, h >>

casA(self) == /\ pc[self] = "casA"
              /\ IF tail = t[self]
                    THEN /\ tail' = t[self] + 1
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ tail' = tail
              /\ IF result'[self]
                    THEN /\ t' = [t EXCEPT ![self] = t[self] + 1]
                         /\ pc' = [pc EXCEPT ![self] = "wt"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "deq"]
                         /\ t' = t
              /\ UNCHANGED << disk, head, enqHistory, deqHistory, terminated, 
                              phaser, condition, tmp, h >>

wt(self) == /\ pc[self] = "wt"
            /\ IF t[self] \notin disk
                  THEN /\ pc' = [pc EXCEPT ![self] = "wt1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "rd"]
            /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, 
                            terminated, phaser, condition, tmp, result, t, h >>

wt1(self) == /\ pc[self] = "wt1"
             /\ IF tail = vio
                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << disk, h >>
                   ELSE /\ IF tail = fin
                              THEN /\ Assert(h[self] = np /\ disk = {}, 
                                             "Failure of assertion at line 367, column 24.")
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << disk, h >>
                              ELSE /\ IF tail = sus
                                         THEN /\ pc' = [pc EXCEPT ![self] = "suspendedA1"]
                                              /\ UNCHANGED << disk, h >>
                                         ELSE /\ IF head = tail - Cardinality(Workers)
                                                    THEN /\ Assert(h[self] = np, 
                                                                   "Failure of assertion at line 388, column 24.")
                                                         /\ pc' = [pc EXCEPT ![self] = "casB"]
                                                         /\ UNCHANGED << disk, 
                                                                         h >>
                                                    ELSE /\ IF h[self] # np /\ h[self] = t[self]
                                                               THEN /\ IncrementStats(20, h[self])
                                                                    /\ disk' = (disk \cup {h[self]})
                                                                    /\ h' = [h EXCEPT ![self] = np]
                                                                    /\ pc' = [pc EXCEPT ![self] = "wt"]
                                                               ELSE /\ IF h[self] # np /\ h[self] > t[self]
                                                                          THEN /\ IncrementStats(21, h[self])
                                                                               /\ disk' = (disk \cup {h[self]})
                                                                               /\ h' = [h EXCEPT ![self] = np]
                                                                               /\ pc' = [pc EXCEPT ![self] = "wt"]
                                                                          ELSE /\ IF h[self] # np /\ h[self] < t[self] /\ head <= tail
                                                                                     THEN /\ IncrementStats(22, h[self])
                                                                                          /\ disk' = (disk \cup {h[self]})
                                                                                          /\ h' = [h EXCEPT ![self] = np]
                                                                                          /\ pc' = [pc EXCEPT ![self] = "wt"]
                                                                                     ELSE /\ TRUE
                                                                                          /\ pc' = [pc EXCEPT ![self] = "wt"]
                                                                                          /\ UNCHANGED << disk, 
                                                                                                          h >>
             /\ UNCHANGED << tail, head, enqHistory, deqHistory, terminated, 
                             phaser, condition, tmp, result, t >>

suspendedA1(self) == /\ pc[self] = "suspendedA1"
                     /\ phaser' = phaser + 1
                     /\ pc' = [pc EXCEPT ![self] = "suspendedB1"]
                     /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, 
                                     terminated, condition, tmp, result, t, h >>

suspendedB1(self) == /\ pc[self] = "suspendedB1"
                     /\ condition \/ terminated
                     /\ phaser' = phaser - 1
                     /\ pc' = [pc EXCEPT ![self] = "wt"]
                     /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, 
                                     terminated, condition, tmp, result, t, h >>

casB(self) == /\ pc[self] = "casB"
              /\ IF tail = t[self]
                    THEN /\ tail' = fin
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ tail' = tail
              /\ IF result'[self]
                    THEN /\ Assert(disk = {}, 
                                   "Failure of assertion at line 391, column 33.")
                         /\ terminated' = TRUE
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "wt"]
                         /\ UNCHANGED terminated
              /\ UNCHANGED << disk, head, enqHistory, deqHistory, phaser, 
                              condition, tmp, t, h >>

rd(self) == /\ pc[self] = "rd"
            /\ Assert(t[self] \in disk, 
                      "Failure of assertion at line 465, column 18.")
            /\ disk' = disk \ {t[self]}
            /\ pc' = [pc EXCEPT ![self] = "exp"]
            /\ UNCHANGED << tail, head, enqHistory, deqHistory, terminated, 
                            phaser, condition, tmp, result, t, h >>

exp(self) == /\ pc[self] = "exp"
             /\ IF TotalWork(head, tail)
                   THEN /\ pc' = [pc EXCEPT ![self] = "deq"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "enq"]
             /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, 
                             terminated, phaser, condition, tmp, result, t, h >>

enq(self) == /\ pc[self] = "enq"
             /\ IF h[self] = np
                   THEN /\ \E i \in SetOfRandomElement(1..50):
                             \/ /\ i \in 1..1
                                /\ pc' = [pc EXCEPT ![self] = "violation"]
                             \/ /\ i \in 2..50
                                /\ pc' = [pc EXCEPT ![self] = "claim"]
                   ELSE /\ IF h[self] # np
                              THEN /\ \E i \in SetOfRandomElement(1..50):
                                        \/ /\ i \in 1..1
                                           /\ pc' = [pc EXCEPT ![self] = "violation"]
                                        \/ /\ i \in 2..2
                                           /\ pc' = [pc EXCEPT ![self] = "deq"]
                                        \/ /\ i \in 3..50
                                           /\ pc' = [pc EXCEPT ![self] = "wrt"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "claim"]
             /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, 
                             terminated, phaser, condition, tmp, result, t, h >>

claim(self) == /\ pc[self] = "claim"
               /\ Assert(h[self] = np, 
                         "Failure of assertion at line 532, column 20.")
               /\ head' = head + 1
               /\ h' = [h EXCEPT ![self] = head']
               /\ \E i \in SetOfRandomElement(2..3):
                    \/ /\ i \in 2..2
                       /\ pc' = [pc EXCEPT ![self] = "deq"]
                    \/ /\ i \in 3..3
                       /\ pc' = [pc EXCEPT ![self] = "wrt"]
               /\ UNCHANGED << tail, disk, enqHistory, deqHistory, terminated, 
                               phaser, condition, tmp, result, t >>

wrt(self) == /\ pc[self] = "wrt"
             /\ disk' = (disk \cup {h[self]})
             /\ h' = [h EXCEPT ![self] = np]
             /\ \E i \in SetOfRandomElement(2..3):
                  \/ /\ i \in 2..2
                     /\ pc' = [pc EXCEPT ![self] = "deq"]
                  \/ /\ i \in 3..3
                     /\ pc' = [pc EXCEPT ![self] = "exp"]
             /\ UNCHANGED << tail, head, enqHistory, deqHistory, terminated, 
                             phaser, condition, tmp, result, t >>

violation(self) == /\ pc[self] = "violation"
                   /\ IF tail = t[self]
                         THEN /\ tail' = vio
                              /\ result' = [result EXCEPT ![self] = TRUE]
                         ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                              /\ tail' = tail
                   /\ IF result'[self]
                         THEN /\ terminated' = TRUE
                              /\ pc' = [pc EXCEPT ![self] = "Done"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "retry"]
                              /\ UNCHANGED terminated
                   /\ UNCHANGED << disk, head, enqHistory, deqHistory, phaser, 
                                   condition, tmp, t, h >>

retry(self) == /\ pc[self] = "retry"
               /\ t' = [t EXCEPT ![self] = tail]
               /\ pc' = [pc EXCEPT ![self] = "violation"]
               /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, 
                               terminated, phaser, condition, tmp, result, h >>

worker(self) == deq(self) \/ suspendedA(self) \/ suspendedB(self)
                   \/ casA(self) \/ wt(self) \/ wt1(self)
                   \/ suspendedA1(self) \/ suspendedB1(self) \/ casB(self)
                   \/ rd(self) \/ exp(self) \/ enq(self) \/ claim(self)
                   \/ wrt(self) \/ violation(self) \/ retry(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ProcName
           \/ (\E self \in Workers: worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ProcName)
        /\ \A self \in Workers : WF_vars(worker(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------

\* This is a clutch, because it is not robust against adding additional
\* variables and omitting to add them to the ViewMap.  Meta-programming for
\* TLA+ would be nice, so we could do something along the lines of:
\* - SelectSeq(vars, LAMBDA e: VarName(e) # "history")
\* It also doesn't work to move the history variable to the top of the spec
\* to make the PlusCal translator generate vars == << history, ...>> and a
\* - SubSeq(vars, 2, Len(vars)), because history is defined in terms of disk.
\* We can't move history to the end, because the worker local variables are
\* generated after the global variables.
\* Lastly, TLC fails to evaluate SelectSeq(vars, LAMBDA e: e # history)
\* because it checks equality for the sequence history with non-seq elements
\* in vars.  I guess, we just have to be diligent or suffer the consequences.
ViewMap == 
  << tail, disk, head, (*history,*) pc, result, t, h, terminated, condition, phaser, tmp >>

\* At the expense of checking this invariant for *every* state (ViewMapOK cannot
\* be an ASSUME because it is state- and not constant-level), we can reliably
\* be warned if we forget to update the ViewMap when variables are added.
ViewMapOK == Len(ViewMap) = Len(vars) - 1

\* Doesn't work because equality for most values of variables undefined.
\*ViewMapOK == Range(ViewMap) = Range(vars) \ {history}

\* Spec /\ Assert(...) works and has the least trade-offs (only evaluated for the
\* initial states as part of the init predicate.
ViewSpec == 
        /\ Spec
        \* Only check the assert once after the initial states have been generated.
        /\ Assert(ViewMapOK, "view map is missing variables.")

\* This is a preliminary/ad-hoc idea to model contention/coherence by disabling
\* actions for a given time frame when they - at the semantical level - executed
\* an expensive operation.  Requires to add a 'blocked' variable and the Read
\* and Write macro and the exp label be amended with a sensible assignment to
\* blocked.
\*Tick ==  /\ blocked' = [ w \in Workers |-> 
\*                               IF blocked[w] = 0 THEN 0 ELSE blocked[w] - 1 ]
\*         /\ UNCHANGED <<disk, h, head, history, pc, result, t, tail>>
\*
\*NonBlockedWorkers == { w \in Workers: blocked[w] = 0 }
\*
\*NextBlocked == \/ (\E self \in NonBlockedWorkers: worker(self)) 
\*               \/ Tick
\*               \/ Terminating
\*
\*SpecBlocked == /\ Init /\ [][NextBlocked]_vars
\*               /\ \A self \in Workers : WF_vars(worker(self))
\*               /\ WF_blocked(Tick)

-----------------------------------------------------------------------------

(* To disable suspension at the algorithm, and, thus, reduce the state space,
   simply re-define ProcName in the model with NoSuspension below. *)
NoSuspension ==
  /\ pc' = [pc EXCEPT !["main"] = "Done"]
  \* This is vars *without* pc (has to be kept up to date with generated vars).
  /\ UNCHANGED << tail, disk, head, enqHistory, deqHistory, terminated, phaser, condition, tmp, result, t, h >>

-----------------------------------------------------------------------------

(***************************************************************************)
(* Definition override for Terminating to print the behavior's history     *)
(* after all workers have terminated.                                      *)
(***************************************************************************)
TerminatingPrint ==
           /\ \A self \in ProcSet: pc[self] = "Done"
           \* Could replace history variable with TLCExt!Trace operator.
           /\ Print(<<"Length: " \o ToString(TLCGet("level")), 
                                         enqHistory \cup deqHistory>>, FALSE)

-----------------------------------------------------------------------------

(***************************************************************************)
(* All workers are in the waiting stage. This is not a livelock and does   *)
(* violate any of the (safety or liveness) properties!                     *)
(***************************************************************************)
AllInWaitStage == Range(pc) \subseteq {"wt","wt1"}

-----------------------------------------------------------------------------

(***************************************************************************)
(* No two workers claimed/hold the same page.                              *)
(***************************************************************************)
ExclusiveEnqueue ==
     \A w, v \in Workers:
           \* Not the same worker
           /\ w # v
           \* No page claimed
           /\ h[w] # np
           /\ h[v] # np
           \* At these labels, races are a property of the algorithm due
           \* to how CAS works.
           /\ pc[w] \notin {"clm1", "clm2"}
           /\ pc[v] \notin {"clm1", "clm2"}
           => h[w] # h[v]

(***************************************************************************)
(* No two workers dequeue the same page.                                   *)
(***************************************************************************)
ExclusiveDequeue == 
     \A w, v \in Workers:
           \* Not the same worker
           /\ w # v
           \* At these two labels, races are a property of the algorithm due
           \* to how CAS works.
           /\ pc[w] \notin {"deq", "casA"}
           /\ pc[v] \notin {"deq", "casA"}
           \* For these special values the property would not hold. The
           \* algorithm re-purposes t to notify other workers when a
           \* violation or termination has been detected (0 is simply
           \* un-initialized). 
           /\ pc[w] \notin {"violation", "Done", "retry"}
           /\ pc[v] \notin {"violation", "Done", "retry"}
           /\ t[w] \notin {0, vio, fin, sus}
           /\ t[v] \notin {0, vio, fin, sus}
           => t[w] # t[v]

-----------------------------------------------------------------------------

(***************************************************************************)
(* Set of workers that are not racing to enqueue (claim) or dequeue pages. *)
(* Workers racing to enqueue a page cannot be part of a livelock but may   *)
(* become so later.                                                        *)
(***************************************************************************)
NonCASWorkers == 
   { w \in DOMAIN pc: pc[w] \notin {"clm1", "clm2", "deq", "casA"} }

RECURSIVE Cycle(_,_,_,_)
Cycle(p, seen, S, T) ==
  \* Hitting np (no-page) implies that there is no livelock.
  IF p = np THEN {}
  ELSE IF p \in seen \/ seen = T
       \* Terminating cases.
       THEN seen \cup {p}
       ELSE IF \E pair \in S: pair[1] = p
            \* Choose from an empty set is bad, hence \E ...
            \* Chop of q from S and recurse.
            THEN LET q == CHOOSE pair \in S: pair[1] = p
                 IN Cycle(q[2], seen \cup {p}, S, T)
            ELSE {}

(***************************************************************************)
(* A livelock is defined to be a cyclic wait-for relationship of N workers *)
(* with N \in 1..Cardinality(Workers). N=1 is considered a trivial         *)
(* livelock (see NonTrivialLivelocks below).                               *)         
(* A livelock occurs if workers busily wait on each others pages.  For     *)
(* example, worker_i has page 42 and waits for page 23. Worker_j has page  *)
(* 23 and waits for page 42.                                               *)
(* Livelocks is a set of disjoint sets where each nested set is the set    *)
(* of pages, which constitute a livelock according to the definiton above. *)
(* The cardinality of a set equals the number of involved workers in the   *)
(* livelock.                                                               *)
(* In trace expressions, this is a useful representation:                  *)
(* [ p \in Range(h) |->                                                    *)
(*     Cycle(p, {}, { <<h[w], t[w]>>: w \in NonCASWorkers },               *)
(*           (Range(h) \cup Range(t)) \ {np}) ]                            *)
(***************************************************************************)
Livelocks == 
  { Cycle(p, {}, { <<h[w], t[w]>>: w \in NonCASWorkers }, 
              (Range(h) \cup Range(t)) \ {np}) : p \in Range(h) } \ {{}}

(***************************************************************************)
(* A trivial livelock is one where a worker waits to dequeue a page that   *) 
(* the worker has claimed itself.                                          *)
(***************************************************************************)
NonTrivialLivelocks ==
  {cycle \in Livelocks: Cardinality(cycle) = 1}

(***************************************************************************)
(* FALSE if all workers are temporarily livelocked. The validity of the    *)
(* Termination property above implies []<>NotAllLivelocked.                *)
(***************************************************************************)
NotAllLivelocked == 
  \A cycle \in Livelocks: Cardinality(cycle) < Cardinality(Workers)

=============================================================================
