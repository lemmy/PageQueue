----------------------------- MODULE PageQueue -----------------------------
EXTENDS Integers, Sequences, SequencesExt, FiniteSets, TLC

(***************************************************************************)
(* The image of the function F.                                            *)
(***************************************************************************)
Image(F) == { F[x] : x \in DOMAIN F }

(***************************************************************************)
(* The sequence seq with e removed or seq iff e \notin Image(seq)          *)
(***************************************************************************)
Remove(seq, e) == SelectSeq(seq, LAMBDA s: s # e)

-----------------------------------------------------------------------------

CONSTANT Pages, Workers

ASSUME /\ Workers # {}                (* at least one worker *)
       /\ Pages \in Nat               (* maximum number of pages to write *)

-----------------------------------------------------------------------------

FINISH  == -1
VIOLATION == -2

-----------------------------------------------------------------------------
(***************************************************************************
--algorithm PageQueue {
       variables \* A strictly monotonic increasing counter
                 tail = 0; 
                 \* A strictly monotonic increasing counter. There is at least a single
                 \* Page available produced by the generation of initial states.
                 pages \in 1..Pages;
                 head = pages; 
                 disk = [ i \in 1..pages |-> i ];
                 history = <<>>;
       
       define {
           TotalWork == Len(history) <= pages
       
           WSafety == 
                   \* Upon terminate all work is either done or a violation has been found.
                   /\ (\A p \in Workers : pc[p] = "Done") => \/ tail = VIOLATION
                                                             \/ /\ tail = FINISH
                                                                /\ disk = <<>>
                   \* There are never duplicates in history nor disk.
                   /\ IsInjective(history)
                   /\ IsInjective(disk)
           
           (* If a violation is found, it is possible that only a single worker explored states ("exp")
              or *)
           WLiveness == /\ \A w \in Workers: pc[w] = "Done" => \/ tail = VIOLATION
                                                               \/ /\ <>(tail = pages /\ head = pages)
                                                                  /\ <>[](tail = FINISH)
                        \* Eventually, all pages have been processed meaning history contains all pages.
                        \* However, since PageQueue relaxes strict FIFO there is no guarantee that pages
                        \* are processed in a deterministic order.  Thus, don't expect an actual order of
                        \* pages which is why history is converted into a set.
           WLiveness2 == /\ <>[](\/ (tail = FINISH /\ Image(history) = 1..pages)
                                 \* Or a violation has been found in which case a prefix of all pages has been processed.
                                 \/ (tail = VIOLATION /\ Image(history) \subseteq 1..pages)) 
                        
       }
       
       (* Atomicity is implicit due to the absence of labels. *)      
       macro CAS(result, var, expected, new) {
           if (var = expected) {
               var := new;
               result := TRUE
           } else { 
               result := FALSE
           }
       }

       \* It is acceptable to deviate from strict FIFO (no strict BFS).
       \* Should it be possible to define a bound for the deviation?
       \* At the implementation level, an enqueue operation is not
       \* atomic but consists of atomically (AtomicLong) incrementing
       \* the enqueue counter head and (re-) naming the disk file.  This
       \* can result in interleavings where a disk file for head is
       \* not yet written but a disk file for head + n already is.  A
       \* dequeue opeartion with head thus cannot make progress while
       \* the dequeue for head + n progresses.
       
       fair process (worker \in Workers) 
            variables result = FALSE, expected = 0; {
            \* Read head and tail to check if work left.
            \* Iff true CAS tail+1, else done. On successful
            \* CAS return tail, else reread head and tail.
            deq: expected := tail;
                 if (expected = VIOLATION \/ expected = FINISH) {
                   goto Done;
                 } else {
                   \* deq/claim and read a page.
                   casA: CAS(result, tail, expected, expected + 1);
                         if (result) {
                            expected := tail;
                            goto wt;
                         } else {
                           (* CAS can fail for two reasons:
                              a) Another worker dequeued the
                                 page (normal case).
                              b) Model checking finished
                                 In both cases return to deq. *)
                            goto deq;
                         };
                 };

            (* spin until a page is available and can be read or
               all other Workers are "stuck" here too in which
               case incidates FINISH. *)
            wt:  while (expected \notin Image(disk)) {
                    if (tail = FINISH \/ tail = VIOLATION) {
                       goto Done;
                    } else if (tail = Cardinality(Workers) + head) {
                       casB: CAS(result, tail, expected, FINISH);
                             if (result) {
                                goto Done;
                             } else {
                                goto wt;
                             }
                    } else {
                       skip; \* goto wt;
                    }
                 };
            rd:  assert expected \in Image(disk);
                 disk := Remove(disk, expected);

            \* Evaluate next-state relation: This a) might
            \* terminate model checking iff a violation is
            \* found, b) no unseen states are found by this
            \* worker, or c) unseen states are found and 
            \* have to be enqueued.
            \* Non-deterministically choose steps.
            exp: history := history \o <<expected>>;
                 (* a) *) either { 
                             casC: CAS(result, tail, expected, VIOLATION);
                                   if (result) {
                                      goto Done;
                                   } else {
                                      retry: expected := tail;
                                             goto casC;
                                   };
                           }
                 (* b) *) or { goto deq; }
                 (* c) *) or { goto enq; };

            (* enq a page. *)
           \* enq is too simple for an actual implementation,
           \* which has to increment head and (re-)name the 
           \* disk file atomically. Otherwise a dequeue operation
           \* might fail to read/find the file.
           \* In the implementation a worker could fully write
           \* (fsync) the file to disk with a temporary name. The
           \* enqueue operation is then limited to the (cheap?)
           \* rename operation (Q: does rename require a disk 
           \* flush?).
           \* It seems impossible to increment high and rename
           \* the disk file atomically if high is represented
           \* by an AtomicLong.  This suggests that enqueue has
           \* to be implemented in a synchronized block/method.
           \* On the other hand, why rename the file at all? Can't
           \* we get away with using an AtomicLong after all if we
           \* keep the mapping from high to the file name in memory?
           \* Idea: Just use an in-memory queue of filenames
           \* (just use Java's BlockingQueue)?
           \* - ArrayBlockingQueue: We want unbound queue
           \* - ConcurrentLinkedQueue: Does not block
           \* - SynchronousQueue: Appears to logically be SPSC
           \* - LinkedBlockingQueue: Memory overhead of creating 
           \*                        linked list nodes.
           \* - PriorityBlockingQueue: Do not need priority (ordering)
           \*                          internally uses Object[]
           \* Alternatively, a dequeue operation could (busy) wait
           \* for the page to become available/visible after it
           \* reads tail successfully.  In other words, dequeue
           \* waits for the corresponding enqueue operation to finish,
           \* which will only ever happen when head and tail are
           \* close. E.g. during the beginning and end of model
           \* checking (to some extend this is what getCache in the
           \* existing implementation is used for).
            enq: CAS(result, head, head, head + 1);
                  if (result) {
                     expected := head;
                     goto wrt;
                  } else {
                     goto enq;
                  };
            
            (* write page to disk *)
            wrt: disk := disk \o << expected >>;
                 goto deq;
       }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES tail, pages, head, disk, history, pc

(* define statement *)
TotalWork == Len(history) <= pages

WSafety ==

        /\ (\A p \in Workers : pc[p] = "Done") => \/ tail = VIOLATION
                                                  \/ /\ tail = FINISH
                                                     /\ disk = <<>>

        /\ IsInjective(history)
        /\ IsInjective(disk)



WLiveness == /\ \A w \in Workers: pc[w] = "Done" => \/ tail = VIOLATION
                                                    \/ /\ <>(tail = pages /\ head = pages)
                                                       /\ <>[](tail = FINISH)




WLiveness2 == /\ <>[](\/ (tail = FINISH /\ Image(history) = 1..pages)

                      \/ (tail = VIOLATION /\ Image(history) \subseteq 1..pages))

VARIABLES result, expected

vars == << tail, pages, head, disk, history, pc, result, expected >>

ProcSet == (Workers)

Init == (* Global variables *)
        /\ tail = 0
        /\ pages \in 1..Pages
        /\ head = pages
        /\ disk = [ i \in 1..pages |-> i ]
        /\ history = <<>>
        (* Process worker *)
        /\ result = [self \in Workers |-> FALSE]
        /\ expected = [self \in Workers |-> 0]
        /\ pc = [self \in ProcSet |-> "deq"]

deq(self) == /\ pc[self] = "deq"
             /\ expected' = [expected EXCEPT ![self] = tail]
             /\ IF expected'[self] = VIOLATION \/ expected'[self] = FINISH
                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "casA"]
             /\ UNCHANGED << tail, pages, head, disk, history, result >>

casA(self) == /\ pc[self] = "casA"
              /\ IF tail = expected[self]
                    THEN /\ tail' = expected[self] + 1
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ tail' = tail
              /\ IF result'[self]
                    THEN /\ expected' = [expected EXCEPT ![self] = tail']
                         /\ pc' = [pc EXCEPT ![self] = "wt"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "deq"]
                         /\ UNCHANGED expected
              /\ UNCHANGED << pages, head, disk, history >>

wt(self) == /\ pc[self] = "wt"
            /\ IF expected[self] \notin Image(disk)
                  THEN /\ IF tail = FINISH \/ tail = VIOLATION
                             THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                             ELSE /\ IF tail = Cardinality(Workers) + head
                                        THEN /\ pc' = [pc EXCEPT ![self] = "casB"]
                                        ELSE /\ TRUE
                                             /\ pc' = [pc EXCEPT ![self] = "wt"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "rd"]
            /\ UNCHANGED << tail, pages, head, disk, history, result, expected >>

casB(self) == /\ pc[self] = "casB"
              /\ IF tail = expected[self]
                    THEN /\ tail' = FINISH
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ tail' = tail
              /\ IF result'[self]
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "wt"]
              /\ UNCHANGED << pages, head, disk, history, expected >>

rd(self) == /\ pc[self] = "rd"
            /\ Assert(expected[self] \in Image(disk), 
                      "Failure of assertion at line 137, column 18.")
            /\ disk' = Remove(disk, expected[self])
            /\ pc' = [pc EXCEPT ![self] = "exp"]
            /\ UNCHANGED << tail, pages, head, history, result, expected >>

exp(self) == /\ pc[self] = "exp"
             /\ history' = history \o <<expected[self]>>
             /\ \/ /\ pc' = [pc EXCEPT ![self] = "casC"]
                \/ /\ pc' = [pc EXCEPT ![self] = "deq"]
                \/ /\ pc' = [pc EXCEPT ![self] = "enq"]
             /\ UNCHANGED << tail, pages, head, disk, result, expected >>

casC(self) == /\ pc[self] = "casC"
              /\ IF tail = expected[self]
                    THEN /\ tail' = VIOLATION
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ tail' = tail
              /\ IF result'[self]
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "retry"]
              /\ UNCHANGED << pages, head, disk, history, expected >>

retry(self) == /\ pc[self] = "retry"
               /\ expected' = [expected EXCEPT ![self] = tail]
               /\ pc' = [pc EXCEPT ![self] = "casC"]
               /\ UNCHANGED << tail, pages, head, disk, history, result >>

enq(self) == /\ pc[self] = "enq"
             /\ IF head = head
                   THEN /\ head' = head + 1
                        /\ result' = [result EXCEPT ![self] = TRUE]
                   ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                        /\ head' = head
             /\ IF result'[self]
                   THEN /\ expected' = [expected EXCEPT ![self] = head']
                        /\ pc' = [pc EXCEPT ![self] = "wrt"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "enq"]
                        /\ UNCHANGED expected
             /\ UNCHANGED << tail, pages, disk, history >>

wrt(self) == /\ pc[self] = "wrt"
             /\ disk' = disk \o << expected[self] >>
             /\ pc' = [pc EXCEPT ![self] = "deq"]
             /\ UNCHANGED << tail, pages, head, history, result, expected >>

worker(self) == deq(self) \/ casA(self) \/ wt(self) \/ casB(self)
                   \/ rd(self) \/ exp(self) \/ casC(self) \/ retry(self)
                   \/ enq(self) \/ wrt(self)

Next == (\E self \in Workers: worker(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Workers : WF_vars(worker(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------

=============================================================================















































F ++ G == IF DOMAIN F = DOMAIN G /\ \A fnc \in {F,G} : \A i \in Image(fnc): i \in Int
          THEN [d \in DOMAIN F |-> F[d] + G[d]]
          ELSE << >>
          
Mrg(F, G) == [d \in DOMAIN F |-> F[d] + G[d]]

vlock == LET clock[i \in DOMAIN TETrace] == lclock(self) IN clock

lclock(proc) == [p \in DOMAIN pc |-> IF p = proc THEN 1 ELSE 0]

self == 
IF TEStateNum = 1
THEN "Init"
ELSE LET this == TETrace[TEStateNum].pc
         prev == TETrace[TEStateNum - 1].pc
     IN CHOOSE p \in DOMAIN prev : prev[p] # this[p]


\*__trace_var_state == 2
\*trace_def_behavior == <<>>
\*
\*self == IF __trace_var_state = 1 THEN "" 
\*        ELSE CHOOSE p \in pc : trace_def_behavior[__trace_var_state - 1][pc] # trace_def_behavior[__trace_var_state][pc]

=============================================================================


viz_clock == TLCSet(42, 1)

viz_counter_set == IF TLCGet(42) <= 16 
                   THEN TLCSet(42, TLCGet(42) + 1)
                   ELSE TRUE
                   
viz_counter_get == TLCGet(42)

viz_behavior_set == LET cnt == TLCGet(42)
                    IN IF TLCGet(42) <= 16
                    THEN TLCSet(23, ([cnt |-> [expected |-> expected, head |-> head] ]))
                    ELSE TRUE

viz_behavior_get == TLCGet(23)

viz_self == IF tail # -1 THEN TLCSet(23, CHOOSE p \in DOMAIN pc : pc[p]' # pc[p]) ELSE TRUE
                 
viz_self_off == IF viz_counter_get = 2
            THEN LET proc == CHOOSE p \in DOMAIN pc : pc[p]' # pc[p]
                 IN TLCSet(23, proc)
            ELSE TRUE
