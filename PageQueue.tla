----------------------------- MODULE PageQueue -----------------------------
EXTENDS Integers, Sequences, SequencesExt, Functions, FiniteSets, TLC, TLCExt

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
         disk \in { 1..i : i \in 1..Pages };
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
       (* 3) enq to wrt: Enqueue a newly generate page.                  *)
       (* In the first state a worker will check for a "fin" or "vio"    *)
       (* signal from another worker.                                    *)
       (******************************************************************)
       fair process (worker \in Workers) 
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
                        history := history \o << Op(self, "enq", h) >>;
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
                 disk := disk \ {t};
                 history := history \o << Op(self, "deq", t) >>;
                 
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
           (*  exactly fits p:  claim, wrt, goto deq | wrt, godo deq       *)
           (*  exceeds page:    claim, wrt, goto enq | wrt, goto enq       *)
           (*                                                              *)
           (*  ("goto enq" means we have to end up claiming a new page!!!) *)
           (****************************************************************)
            enq: if (h = np) {
                      either { goto violation; } or { goto claim; };
                 } else if (h # np) {
                      either { goto violation; } or { goto wrt; } or { goto deq; };
                 };

            claim: assert h = np;
                   clm1:  h := head;
                   clm2:  CAS(result, head, h, h + 1);
                          if (result) {
                             h := h + 1;
                             either { goto deq; } 
                                 or { goto wrt; };
                          } else {
                              goto clm1;
                          };
            
            (*************************************************************)
            (* Write page to disk. Intuitively, one would write the page *)
            (* first (wrt) before enqueueing it (enq). However, enq      *)
            (* determines the identifier (e.g. file-name) of the page.   *)
            (*************************************************************)
            wrt: disk := disk \cup {h};
                 history := history \o << Op(self, "enq", h) >>;
                 h := np;
                 either { goto deq; } or { goto exp; };
                     
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1230f66c93497b1a9d145cd9cbbbf4a1
VARIABLES tail, disk, head, history, pc

(* define statement *)
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
        /\ disk \in { 1..i : i \in 1..Pages }
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
                                             "Failure of assertion at line 195, column 20.")
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
                                             "Failure of assertion at line 231, column 24.")
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << disk, history, h >>
                              ELSE /\ IF head = tail - Cardinality(Workers)
                                         THEN /\ Assert(h[self] = np, 
                                                        "Failure of assertion at line 247, column 24.")
                                              /\ pc' = [pc EXCEPT ![self] = "casB"]
                                              /\ UNCHANGED << disk, history, h >>
                                         ELSE /\ IF h[self] # np /\ head <= tail
                                                    THEN /\ disk' = (disk \cup {h[self]})
                                                         /\ history' = history \o << Op(self, "enq", h[self]) >>
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
                                   "Failure of assertion at line 250, column 33.")
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "wt"]
              /\ UNCHANGED << disk, head, history, t, h >>

rd(self) == /\ pc[self] = "rd"
            /\ Assert(t[self] \in disk, 
                      "Failure of assertion at line 297, column 18.")
            /\ disk' = disk \ {t[self]}
            /\ history' = history \o << Op(self, "deq", t[self]) >>
            /\ pc' = [pc EXCEPT ![self] = "exp"]
            /\ UNCHANGED << tail, head, result, t, h >>

exp(self) == /\ pc[self] = "exp"
             /\ IF TotalWork
                   THEN /\ pc' = [pc EXCEPT ![self] = "deq"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "enq"]
             /\ UNCHANGED << tail, disk, head, history, result, t, h >>

enq(self) == /\ pc[self] = "enq"
             /\ IF h[self] = np
                   THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "violation"]
                           \/ /\ pc' = [pc EXCEPT ![self] = "claim"]
                   ELSE /\ IF h[self] # np
                              THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "violation"]
                                      \/ /\ pc' = [pc EXCEPT ![self] = "wrt"]
                                      \/ /\ pc' = [pc EXCEPT ![self] = "deq"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "claim"]
             /\ UNCHANGED << tail, disk, head, history, result, t, h >>

claim(self) == /\ pc[self] = "claim"
               /\ Assert(h[self] = np, 
                         "Failure of assertion at line 336, column 20.")
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
                         /\ \/ /\ pc' = [pc EXCEPT ![self] = "deq"]
                            \/ /\ pc' = [pc EXCEPT ![self] = "wrt"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "clm1"]
                         /\ h' = h
              /\ UNCHANGED << tail, disk, history, t >>

wrt(self) == /\ pc[self] = "wrt"
             /\ disk' = (disk \cup {h[self]})
             /\ history' = history \o << Op(self, "enq", h[self]) >>
             /\ h' = [h EXCEPT ![self] = np]
             /\ \/ /\ pc' = [pc EXCEPT ![self] = "deq"]
                \/ /\ pc' = [pc EXCEPT ![self] = "exp"]
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4c66a6a49c34790f83720dd8ffeadc2d
-----------------------------------------------------------------------------


=============================================================================
