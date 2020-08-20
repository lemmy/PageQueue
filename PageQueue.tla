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
Op(t, o, p) == [ thread |-> t, oper |-> o, page |-> p ]

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
\*   generating a suffix of stuttering steps up to -depth N. 
\* -- Action Constraint: ~Terminating
\* - Increase -depth to a large value 
\* - Amend behavior spec to initialize TLCSet registers:
\* -- InitializeStats /\ Spec
\* - Add PrintStats as Post Condition on TLC Options page of model
\* - Re-define SetOfRandomElement and SetOfInitialDisks in model

SetOfRandomElement(S) == S \* Redefine to {RandomElement(S)} in model for simulation.

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
   LET R == Cardinality(Workers)
   IN /\ \A n \in (1..R \cup 20..22): TLCSet(n, 0)

(****************************************************************************)
(* Print the value of all registers/for all values in the range of w2i.     *)
(* Should be evaluated as a POSTCONDITION in the model's config file.       *)
(****************************************************************************)
PrintStats == 
     /\ \A w \in Workers: PrintT(<<w, TLCGet(w2i[w])>>)
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
IncrementStats(w) == IF w < 20 THEN TLCDefer(TLCSet(w2i[w], TLCGet(w2i[w]) + 1))
                     ELSE TLCDefer(TLCSet(w, TLCGet(w) + 1))

-----------------------------------------------------------------------------

(******************************************************************)
(* Hint: Separation into Finish and Violation not needed by the   *)
(* implementation. The implementation just returns null. Instead, *)
(* only the spec uses it to be able to state stronger invariants. *)
(******************************************************************)
fin == CHOOSE fin : fin \notin Nat
vio == CHOOSE vio : vio \notin Nat \cup {fin}
np  == CHOOSE np  : np  \notin Nat \cup {fin,vio}

-----------------------------------------------------------------------------

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
         history = [ i \in 1..Cardinality(disk) |-> Op("init", "enq", i) ];
       
       define {
           appendHistory(p,o,h) == history \o << Op(p, o, h) >>
           (*******************************************************************)
           (* The sequence of enqueued pages and dequeued pages respectively. *)
           (*******************************************************************)
           Enqueued == Reduce(SelectSeq(history, LAMBDA e : e["oper"]="enq"), "page")
           Dequeued == Reduce(SelectSeq(history, LAMBDA e : e["oper"]="deq"), "page")
       
           (*****************************************************************)
           (* Make state space explicitly finite (see enq) instead of       *)
           (* with a state constraint that interfers with liveness checking.*)
           (*****************************************************************)
           TotalWork == Len(Enqueued) > Pages \/ Len(Dequeued) > Pages
       
           (******************************)
           (* Type correctness invariant *)
           (******************************)
           TypeOK == 
                 /\ tail \in (Nat \cup {fin,vio})
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
                   (**********************************************************)
                   (* Neither the enqueued operations nor the dequeued pages *)
                   (* ever contain duplicates.                               *)
                   (**********************************************************)
                   /\ IsInjective(Enqueued)
                   /\ IsInjective(Dequeued)
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
                          /\ Range(Enqueued) = Range(Dequeued)
                          (************************************************************)
                          (* Due to the way how we made the state space of the spec   *)
                          (* finite, admissible behaviors can create more pages. I'm  *)
                          (* too lazy to find the actual bound.                       *)
                          (************************************************************)
                          /\ 1..Pages \subseteq Range(Reduce(history, "page"))
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


\*  If suspension is picked up again, the following branch contains the prototype of a
\*  PCal 'action' keyword:
\*  https://github.com/lemmy/tlaplus/tree/mku-pcal-action-keyword
\*  https://github.com/lemmy/PageQueue/commit/07d2ea57a19baf003b18868f2669cf05fddec0d2
\*       fair process (ProcName = "main") 
\*            variables tmp = -1; {
\*            
\*            m0:  while (TRUE) {
\*                         (* CAS tail to SUSPEND and remember old value *)
\*                     m1: tmp := tail;
\*                         tail := SUSPEND;
\*                         \* Setting tail to SUSPEND is to simple because it
\*                         \* does not take into account that tail could already
\*                         \* be set to fin in which case we must not suspend.
\*                         (* Setting tail to SUSPEND might override fin/vio  *)
\*                         (* set by a worker.  Thus, check for override and set tail  *)
\*                         (* from SUSPEND back to tmp. Afterwards, also terminate the *)
\*                         (* the phaser to release any worker we might have caused to *)
\*                         (* suspend instead of finish.                               *)
\*                     m2: if (tmp = vio \/ tmp = fin) {
\*                             tail := tmp;
\*                             goto Done;
\*                         };
\*                     m3: await AAAA;
\*                         (* Do main thread things and set tail back to t. *)
\*                     m4: skip;
\*                         tail := tmp;
\*                         (* Resume workers. *)
\*                         (* Phaser#arriveAndAwaitAdvance *)
\*                     m5: await AAAB;
\*            };
\*       }
       
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
\*                 } else if (t = SUSPEND) {
\*                     awtwtA: await AAAA;
\*                     awtwtB: await AAAB;
\*                     goto deq;
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
                       assert disk = {};
                       goto Done;
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
                       (*      fin before us (if which case we can go to      *)
                       (*      Done). This optimization is more about elegance*)
                       (*      than about performance though.                 *)
                       (*******************************************************)
                       assert h = np;
                       casB: CAS(result, tail, t, fin);
                             if (result) {
                                assert disk = {};
                                goto Done;
                             } else {
                                (************************************************)
                                (* Failed to signal termination because another *)
                                (* worker signaled termination first.           *)
                                (************************************************)
                                goto wt;
                             }
                    } else if (h # np /\ head <= tail) {
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
                        disk := disk \cup {h};
                        history := appendHistory(self, "enq", h);
                        h := np;
                        goto wt;
                    } else if (h # np) {
                        await IncrementStats(self);
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
                 disk := disk \ {t};
                 history := appendHistory(self, "deq", t);
                 
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
            exp: if (TotalWork) {
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
                            or { await i \in 2..48; goto claim; };
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
                             (* Current page is full, thus write it to disk *) 
                             or { await i \in 2..48;  goto wrt; } 
                             (* Set of successor states is empty (no succ). *)
                             or { await i \in 49..50; goto deq; };
                      }
\*                         either { goto violation; } 
\*                             or { goto wrt; } 
\*                             or { goto deq; };
                 };

            claim: assert h = np;
                   \* This could perhaps be refactored to fence-and-add,
                   \* because the h/head variable is always monotonically
                   \* increasing and we don't need to check its value for
                   \* a special flag such as vio, fin, ...
                   \* It would reduce the spec's state space and require
                   \* fewer instructions in an implementation. 
                   clm1:  h := head;
                   clm2:  CAS(result, head, h, h + 1);
                          if (result) {
                             h := h + 1;
                             with ( i \in SetOfRandomElement(1..2) ) {
                                 (* set of successor states fits into  *)
                                 (* page, thus no need to write page.  *)
                                 either { await i \in 1..1; goto deq; } 
                                 (* set of successor states does not fit *)
                                 (* into page, thus write it.            *)
                                     or { await i \in 2..2; goto wrt; };
                             }
\*                                 either { goto deq; } 
\*                                     or { goto wrt; };
                          } else {
                              goto clm1;
                          };
            
            (*************************************************************)
            (* Write page to disk. Intuitively, one would write the page *)
            (* first (wrt) before enqueueing it (enq). However, enq      *)
            (* determines the identifier (e.g. file-name) of the page.   *)
            (*************************************************************)
            wrt: disk := disk \cup {h};
                 history := appendHistory(self, "enq", h);
                 h := np;
                 with ( i \in SetOfRandomElement(1..2) ) {
                      (* With the current page written and done, either  *)
                      (* go to dequeue a new page or explore additional  *)
                      (* states. The latter models the case where the    *)
                      (* set of successor states doesn't fit into a      *)
                      (* single page.                                    *)
                      either { await i \in 1..1; goto deq; } 
                          or { await i \in 2..2; goto exp; };
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
                             goto Done;
                       } else {
                             retry: t := tail;
                             goto violation;
                       };           
       }
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "fa8db8dd" /\ chksum(tla) = "3c332264")
VARIABLES tail, disk, head, history, pc

(* define statement *)
appendHistory(p,o,h) == history \o << Op(p, o, h) >>



Enqueued == Reduce(SelectSeq(history, LAMBDA e : e["oper"]="enq"), "page")
Dequeued == Reduce(SelectSeq(history, LAMBDA e : e["oper"]="deq"), "page")





TotalWork == Len(Enqueued) > Pages \/ Len(Dequeued) > Pages




TypeOK ==
      /\ tail \in (Nat \cup {fin,vio})
      /\ head \in NatP
      /\ disk \subseteq NatP








WSafety ==




        /\ IsInjective(Enqueued)
        /\ IsInjective(Dequeued)





        /\ (\A p \in Workers : pc[p] = "Done") =>
            \/ tail = vio
            \/ /\ tail = fin
               /\ disk = {}



               /\ Range(Enqueued) = Range(Dequeued)





               /\ 1..Pages \subseteq Range(Reduce(history, "page"))

VARIABLES result, t, h

vars == << tail, disk, head, history, pc, result, t, h >>

ProcSet == (Workers)

Init == (* Global variables *)
        /\ tail = 0
        /\ disk \in SetOfInitialDisks
        /\ head = Max(disk)
        /\ history = [ i \in 1..Cardinality(disk) |-> Op("init", "enq", i) ]
        (* Process worker *)
        /\ result = [self \in Workers |-> FALSE]
        /\ t = [self \in Workers |-> 0]
        /\ h = [self \in Workers |-> np]
        /\ pc = [self \in ProcSet |-> "deq"]

deq(self) == /\ pc[self] = "deq"
             /\ t' = [t EXCEPT ![self] = tail]
             /\ IF t'[self] = vio
                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                   ELSE /\ IF t'[self] = fin
                              THEN /\ Assert(disk = {}, 
                                             "Failure of assertion at line 256, column 20.")
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "casA"]
             /\ UNCHANGED << tail, disk, head, history, result, h >>

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
              /\ UNCHANGED << disk, head, history, h >>

wt(self) == /\ pc[self] = "wt"
            /\ IF t[self] \notin disk
                  THEN /\ pc' = [pc EXCEPT ![self] = "wt1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "rd"]
            /\ UNCHANGED << tail, disk, head, history, result, t, h >>

wt1(self) == /\ pc[self] = "wt1"
             /\ IF tail = vio
                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << disk, history, h >>
                   ELSE /\ IF tail = fin
                              THEN /\ Assert(disk = {}, 
                                             "Failure of assertion at line 292, column 24.")
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << disk, history, h >>
                              ELSE /\ IF head = tail - Cardinality(Workers)
                                         THEN /\ Assert(h[self] = np, 
                                                        "Failure of assertion at line 308, column 24.")
                                              /\ pc' = [pc EXCEPT ![self] = "casB"]
                                              /\ UNCHANGED << disk, history, h >>
                                         ELSE /\ IF h[self] # np /\ h[self] = t[self]
                                                    THEN /\ disk' = (disk \cup {h[self]})
                                                         /\ history' = appendHistory(self, "enq", h[self])
                                                         /\ h' = [h EXCEPT ![self] = np]
                                                         /\ pc' = [pc EXCEPT ![self] = "wt"]
                                                    ELSE /\ IF h[self] # np /\ h[self] > t[self]
                                                               THEN /\ disk' = (disk \cup {h[self]})
                                                                    /\ history' = appendHistory(self, "enq", h[self])
                                                                    /\ h' = [h EXCEPT ![self] = np]
                                                                    /\ pc' = [pc EXCEPT ![self] = "wt"]
                                                               ELSE /\ IF h[self] # np /\ h[self] < t[self] /\ head <= tail
                                                                          THEN /\ disk' = (disk \cup {h[self]})
                                                                               /\ history' = appendHistory(self, "enq", h[self])
                                                                               /\ h' = [h EXCEPT ![self] = np]
                                                                               /\ pc' = [pc EXCEPT ![self] = "wt"]
                                                                          ELSE /\ TRUE
                                                                               /\ pc' = [pc EXCEPT ![self] = "wt"]
                                                                               /\ UNCHANGED << disk, 
                                                                                               history, 
                                                                                               h >>
             /\ UNCHANGED << tail, head, result, t >>

casB(self) == /\ pc[self] = "casB"
              /\ IF tail = t[self]
                    THEN /\ tail' = fin
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ tail' = tail
              /\ IF result'[self]
                    THEN /\ Assert(disk = {}, 
                                   "Failure of assertion at line 311, column 33.")
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "wt"]
              /\ UNCHANGED << disk, head, history, t, h >>

rd(self) == /\ pc[self] = "rd"
            /\ Assert(t[self] \in disk, 
                      "Failure of assertion at line 383, column 18.")
            /\ disk' = disk \ {t[self]}
            /\ history' = appendHistory(self, "deq", t[self])
            /\ pc' = [pc EXCEPT ![self] = "exp"]
            /\ UNCHANGED << tail, head, result, t, h >>

exp(self) == /\ pc[self] = "exp"
             /\ IF TotalWork
                   THEN /\ pc' = [pc EXCEPT ![self] = "deq"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "enq"]
             /\ UNCHANGED << tail, disk, head, history, result, t, h >>

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
                                        \/ /\ i \in 2..45
                                           /\ pc' = [pc EXCEPT ![self] = "wrt"]
                                        \/ /\ i \in 46..50
                                           /\ pc' = [pc EXCEPT ![self] = "deq"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "claim"]
             /\ UNCHANGED << tail, disk, head, history, result, t, h >>

claim(self) == /\ pc[self] = "claim"
               /\ Assert(h[self] = np, 
                         "Failure of assertion at line 436, column 20.")
               /\ pc' = [pc EXCEPT ![self] = "clm1"]
               /\ UNCHANGED << tail, disk, head, history, result, t, h >>

clm1(self) == /\ pc[self] = "clm1"
              /\ h' = [h EXCEPT ![self] = head]
              /\ pc' = [pc EXCEPT ![self] = "clm2"]
              /\ UNCHANGED << tail, disk, head, history, result, t >>

clm2(self) == /\ pc[self] = "clm2"
              /\ IF head = h[self]
                    THEN /\ head' = h[self] + 1
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ head' = head
              /\ IF result'[self]
                    THEN /\ h' = [h EXCEPT ![self] = h[self] + 1]
                         /\ \E i \in SetOfRandomElement(1..2):
                              \/ /\ i \in 1..1
                                 /\ pc' = [pc EXCEPT ![self] = "deq"]
                              \/ /\ i \in 2..2
                                 /\ pc' = [pc EXCEPT ![self] = "wrt"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "clm1"]
                         /\ h' = h
              /\ UNCHANGED << tail, disk, history, t >>

wrt(self) == /\ pc[self] = "wrt"
             /\ disk' = (disk \cup {h[self]})
             /\ history' = appendHistory(self, "enq", h[self])
             /\ h' = [h EXCEPT ![self] = np]
             /\ \E i \in SetOfRandomElement(1..2):
                  \/ /\ i \in 1..1
                     /\ pc' = [pc EXCEPT ![self] = "deq"]
                  \/ /\ i \in 2..2
                     /\ pc' = [pc EXCEPT ![self] = "exp"]
             /\ UNCHANGED << tail, head, result, t >>

violation(self) == /\ pc[self] = "violation"
                   /\ IF tail = t[self]
                         THEN /\ tail' = vio
                              /\ result' = [result EXCEPT ![self] = TRUE]
                         ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                              /\ tail' = tail
                   /\ IF result'[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "retry"]
                   /\ UNCHANGED << disk, head, history, t, h >>

retry(self) == /\ pc[self] = "retry"
               /\ t' = [t EXCEPT ![self] = tail]
               /\ pc' = [pc EXCEPT ![self] = "violation"]
               /\ UNCHANGED << tail, disk, head, history, result, h >>

worker(self) == deq(self) \/ casA(self) \/ wt(self) \/ wt1(self)
                   \/ casB(self) \/ rd(self) \/ exp(self) \/ enq(self)
                   \/ claim(self) \/ clm1(self) \/ clm2(self) \/ wrt(self)
                   \/ violation(self) \/ retry(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Workers: worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Workers : WF_vars(worker(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------

(***************************************************************************)
(* Definition override for Terminating to print the behavior's history     *)
(* after all workers have terminated.                                      *)
(***************************************************************************)
TerminatingPrint ==
           /\ \A self \in ProcSet: pc[self] = "Done"
           /\ Print(<<"Length: " \o ToString(TLCGet("level")), history>>, FALSE)

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
           /\ t[w] \notin {0, vio, fin}
           /\ t[v] \notin {0, vio, fin}
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
