(***************************************************************************)
Random Thoughts:
----------------

- The lower bound of a page is a single state.  The upper bound is chosen s.t. 
  work is evenly distributed across workers.  This is probably going to be a function
  whose input is the average outdegree of the state graph.

- A page is of variable size both in terms of the number of states it contains
  as well as its byte-size on disk.  The former is determined by the number of states
  generated by a worker as part of the evaluation of the next-state relation.  The
  latter is determined by the size of the state's variables and the efficiency of
  object serialzation (ie compression).

- Determining the queue's global size is difficult: Maintaining an exact counter of
  unseen states would require synchronization of the counter and the queue.  An 
  approximation of the queue's size is however easily accomplished with an AtomicLong.

- Using two AtomicLongs, to represent the head and tail pages of the queue, has a fixed
  memory/space requirement whereas the space requirement of a queue of page handles
  (filenames) is linear in the number of (unseen) pages.  Most off-the-shelf queue
  implementations have significant overhead too bc they e.g. wrap each element in a
  linkedlist node.

- Let the first generation of pages be those when head - tail = 1.  In other words pages
  are produced and consumed at a similar rate.  This is the case at the beginning of model
  checking.  It would be desirable to create the first generation of pages in memory to
  not cause disk IO.  This property would mean that the page queue is usable even when
  model checking small state spaces.

- Worker suspension/resume can probably be implemented by a RW lock where workers acquire
  and hold the read lock and the thread requesting suspension acquires the write lock.
  On the other hand, adding a separate synchronization primitive (locks) into the game
  might make the algorithm more complicated: suspension can likely be handled by signaling
  it via the tail AtomicLong (it is already used for other signals such as termination...).  

---

The algorithm relys on two synchronization primitives:

a) Atomic counters (two) implemented with Java's AtomicLong
b) Atomic file rename operation implemented with Java's java.nio.Files#move
   (java.nio.file.StandardCopyOption.ATOMIC_MOVE)

---

Fixed-size vs. upper size vs. dynamic page sizes

An always full, fixed-size page is impossible because the actual number of successor
states is not guaranteed to align with the page size.  Determining the page size
dynamically---based on the number of successor states---has the disadvantage that we
end up with tiny pages when we optimize for huge pages if states have few successors.
Thus, we allocate fixed-size pages, which we try to fill up if possible.  This means
that we potentially enqueue a page after we have dequeued many (all) other pages.   

---

This algorithm works---all pages get explored and threads terminate afterwards---because
the ratio between dequeues and enqueues is an invariant.  Each dequeue operation is
always followed by an enqueue operation.  When head >= tail, we know that not all work
is done. When tail > head /\ tail < head + Cardinality(Workers), a subset of the
workers are waiting for new pages.  FINISH iff tail = head + Cardinality(Workers).

Disk to be empty is a necessary but not a sufficient condition for termination (the
last page might have been dequeued and the new page---with the successor states---has
not yet been enqueued).

Fixed-sized pages:
+ Ease memory-allocation (less fragmentation)
+ Reuse allocate pages (a deqeued page can become the next enqueue page (with the
  old states replaced)
+ Page compaction (ie. "symbolification") probably more effective with fixed-size,
  large pages

    This commit marks the end of the design with a dynamic page
    size (the size of a page is determined by the number of
    successor states generated).  The next design will model
    fixed-size pages that TLC will try to fill up if possible.
    From the perspective of the lock-free protocol, this means
    that it changes from an alternation between dequeue and enqueue
    operation to one where multiple dequeue operations are
    followed by a single enqueue operation.

Fixed-size pages only covers half of the story. It is really about filling up pages
as an optimization by reducing the overall number of pages.  Fewer pages means fewer
IO overhead of creating, deleting, ... files.  In order to fill up pages, we have to
switch from pairs of enq and deq operations to a 1:n ratio where n \in 0..  

Todo:
-----

Worker suspension as prototyped in
https://github.com/lemmy/PageQueue/commit/f2b4b3ba1cf77aa5683873de28873d53ad231be1

This can likely be done with a high-level synchronization primitive such as a
barrier implemented by a (Java) phaser.  A first version has been speced with
the main process but abandoned for now.
 
(***************************************************************************)


----------------------------- MODULE PageQueue -----------------------------
EXTENDS Integers, Sequences, SequencesExt, Functions, FiniteSets, TLC, Naturals

\* TODO: Separation into Finish and Violation not needed by the implementation.
\* The implementation just returns null. Instead, only the spec uses it to
\* be able to state stronger invariants. 
CONSTANT Pages, Workers, FINISH, VIOLATION

ASSUME /\ Workers # {}                (* at least one worker *)
       /\ Pages \in Nat               (* maximum number of pages to write *)

-----------------------------------------------------------------------------
(***************************************************************************)
(*  PageQueue models a non-strict/relaxed FIFO/queue specially tailored to *)
(*  the TLC  model checker.  TLC generates large volumes of unexplored     *)
(*  states during breadth-first search of the (on-the-fly generated) state *)
(*  graph.  In order to parallelize the BFS search and ultimately scale    *)
(*  it, we accept to deviate from strict fifo order.                       *)
(*                                                                         *)
(*  The underlying assumption/justification/argument is as follows:        *)
(*  1) TLC employs BFS instead of DFS to check safety properties because:  *)
(*  1a) BFS is parallelizable and thus scales better with the number of    *)
(*      cores.                                                             *)  
(*  1b) Users of TLC are interested in finding the shortest                *) 
(*      counter-example if any,  because a counter-example with a hundred  *)
(*      states is more difficult to understand than one with 10 states.    *)
(*  2) An approximation of the shortest counter-example is acceptable      *)
(*     provided its upper bound (the approximation cannot be shorter than  *)
(*     the actual counter-example) is within  1-2 states. WE WILL EXPLORE  *)
(*     IF THIS IS SOMETHING THAT CAN BE GUARANTEED WITH CERTAINTY OR JUST  *)
(*     HIGH PROBABILITY.                                                   *)
(*  3) The average state graph is such that it has a low diameter and      *)
(*     states have a high outdegree.  In other words, it  has many states  *)
(*     with identical distance d from the initial states (root nodes of    *)
(*     the graph).                                                         *)
(*  4) A page is thus a sequence of states which - with high probability - *)
(*     have all the same d.                                                *)
(*  5) Assuming we choose (limit) the size of a page s.t. processes will   *)
(*     dequeue pages with distance [d-2,d+2].                              *)
(*                                                                         *)
(*     The fundamental idea of PageQueue is to improve scalability by      *)
(*     minimizing the critical section to incrementing counters whereas    *)
(*     the existing implementation of TLC runs IO (read/write states)      *)
(*     inside the CS.                                                      *)
(***************************************************************************)


Disks == { [ n \in s |-> n ]  : s \in { (1..n) : n \in (1..Pages) } }

Max(seq) == CHOOSE s \in Range(seq) : \A e \in Range(seq) : s >= e
-----------------------------------------------------------------------------

(***************************************************************************
--algorithm PageQueue {
       variables \* A strictly monotonic increasing counter. Its value marks the
                 \* last page that has been consumed.  Iff its value is negativ,
                 \* it serves as a signal for consumers/workers (compare FINISH and VIOLATION).
                 tail = 0; \* No page has been dequeued yet.
                 \* The pages that have been swapped to disk.
                 disk \in Disks; \* The initial page is initially on-disk.
                 \* A strictly monotonic increasing counter. Its value marks the
                 \* last page that has been consumed.
                 head = Max(disk); \* A single page with the initial states has been enqueued.
                 \* Auxiliary/History variable to check properties.
                 history = <<>>;
       
       define {
           \* PCal translator generates ProcSet below definitions, yet the invariants use it.
           MyProcSet == (*{"main"} \cup *)Workers
           
           ArriveAndAwait(F) == /\ \A p \in MyProcSet : pc[p] \in DOMAIN F
                                /\ pc' = [ p \in MyProcSet |-> F[pc[p]] ]
       
           AAAA == ArriveAndAwait([ m3 |-> "m4", Done |-> "Done" , awtwtA |-> "awtwtB" ])
           AAAB == ArriveAndAwait([ m5 |-> "m0", Done |-> "Done" , awtwtB |-> "deq" ])
       
           \* state constraint
           TotalWork == Len(history) <= Pages
       
           \* Safety Property:
           \* There are never duplicates in history nor disk.
           \* Upon terminate all work is either done or a violation has been found.
           WSafety == 
                   /\ IsInjective([ i \in 1..Len(history) |-> history[i][2] ])
                   /\ IsInjective(disk)
                   /\ (\A p \in MyProcSet : pc[p] = "Done") => \/ tail = VIOLATION
                                                               \/ /\ tail = FINISH
                                                                  /\ disk = <<>>
           
           \* If a violation is found, it is possible that only a single worker explored states ("exp")
           WLiveness == /\ \A w \in MyProcSet: pc[w] = "Done" => \/ tail = VIOLATION
                                                                 \/ /\ <>(tail = Pages /\ head = Pages)
                                                                    /\ <>[](tail = FINISH)

           \* Eventually, all pages have been processed meaning history contains all pages.
           \* However, since PageQueue relaxes strict FIFO there is no guarantee that pages
           \* are processed in a deterministic order.  Thus, don't expect an actual order of
           \* pages which is why history is converted into a set.
           \* Or a violation has been found in which case a prefix of all pages has been processed.
           WLiveness2 == /\ <>[](\/ (tail = FINISH /\ Range(history) = 1..Pages)
                                 \/ (tail = VIOLATION /\ Range(history) \subseteq 1..Pages)) 
                        
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
\*       
\*       fair process (ProcName = "main") 
\*            variables tmp = -1; {
\*            
\*            m0:  while (TRUE) {
\*                         (* CAS tail to SUSPEND and remember old value *)
\*                     m1: tmp := tail;
\*                         tail := SUSPEND;
\*                         \* Setting tail to SUSPEND is to simple because it
\*                         \* does not take into account that tail could already
\*                         \* be set to FINISH in which case we must not suspend.
\*                         (* Setting tail to SUSPEND might override FINISH/VIOLATION  *)
\*                         (* set by a worker.  Thus, check for override and set tail  *)
\*                         (* from SUSPEND back to tmp. Afterwards, also terminate the *)
\*                         (* the phaser to release any worker we might have caused to *)
\*                         (* suspend instead of finish.                               *)
\*                     m2: if (tmp = VIOLATION \/ tmp = FINISH) {
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

       \* It is acceptable to deviate from strict FIFO (no strict BFS).
       \* Should it be possible to define a bound for the deviation?
       \* At the implementation level, an enqueue operation is not
       \* atomic but consists of atomically (AtomicLong) incrementing
       \* the enqueue counter head and (re-) naming the disk file.  This
       \* can result in interleavings where a disk file for head is
       \* not yet written but a disk file for head + n already is.  A
       \* dequeue opeartion with head thus cannot make progress while
       \* the dequeue for head + n progresses.
       
       (* A worker process has the following high-level stages: *)
       (* - deq to rd:  Dequeue a page iff one is available. *)
       (* - exp:        Evaluate the next-state relation. *)
       (* - enq to wrt: Enqueue a newly generate page. *)
       (* In all of the stages, it is possible for a worker to terminate *)
       (* on a violation of an invariant or be terminated by receiving a *)
       (* signal from another worker. *)
       fair process (worker \in Workers) 
            variables result = FALSE, t = 0, h = 0; {
            
            (* 1. Stage *)
            
            \* Read head and tail to check if work left.
            \* Iff true CAS tail+1, else done. On successful
            \* CAS return tail, else reread head and tail.
            deq: t := tail;
                 if (t = VIOLATION) {
                   goto Done;
                 } else if (t = FINISH) {
                   assert disk = <<>>;
                   goto Done;
\*                 } else if (t = SUSPEND) {
\*                     awtwtA: await AAAA;
\*                     awtwtB: await AAAB;
\*                     goto deq;
                 } else {
                   \* deq/claim a page (and subsequently at wt read it).
                   casA: CAS(result, tail, t, t + 1);
                         if (result) {
                            (* Set t to value CASed. *)
                            t := t + 1;
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
               all other Workers are "stuck" here too (which
               incidates FINISH). *)
            wt: while (t \notin Range(disk)) {
            wt1:   if (tail = VIOLATION) {
                       \* Another worker signaled termination.
                       goto Done;
                    } else if (tail = FINISH) {
                       assert disk = <<>>;
                       goto Done;
                    } else if (tail = Cardinality(Workers) + head) {
                       \* This worker detected the termination condition.
                       casB: CAS(result, tail, t, FINISH);
                             if (result) {
                                \* Successfully signaled termination.
                                assert disk = <<>>;
                                goto Done;
                             } else {
                                \* Failed to signal termination.
                                goto wt;
                             }
                    } else {
                       \* Page not yet readable (the writer hasn't finished yet). 
                       skip; \* goto wt;
                    }
                 };
            rd:  assert t \in Range(disk);
                 disk := Remove(disk, t);

            (* 2. Stage *)

            \* Evaluate next-state relation: This a) might
            \* terminate model checking iff a violation is
            \* found, b) no unseen states are found by this
            \* worker, or c) unseen states are found and 
            \* have to be enqueued.
            \* Non-deterministically choose steps.
            exp: history := history \o << <<self, t>> >>;
                 if (Len(history) > Pages) {
                          \* Bound spec to a finite state space. 
                          \* Using a state constraint such as 
                          \* Len(history) < Pages is more elegant
                          \* but causes trouble when checking
                          \* liveness because the property is
                          \* vacuously true.  
                          goto deq;
                 } else {
                 (* c) *) either { goto enq; };
                 (* b) *) or { goto deq; };
                 (* a) *) or { casC: CAS(result, tail, t, VIOLATION);
                                     if (result) {
                                        goto Done;
                                     } else {
                                        retry: t := tail;
                                               goto casC;
                                     };
                             };
                 };


           (* 3. Stage *)
            
           (* enqueue a page. *)
           \* enq ideally increments head and (re-)names the 
           \* disk file atomically. Otherwise a dequeue operation
           \* might fail to read/find the file if it claims the
           \* page (inc tail) before the page is written.
           \*
           \* However, It seems impossible to increment high and
           \* rename the disk file atomically if high is represented
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
            enq: h := head;
            enq2: CAS(result, head, h, h + 1);
                  if (result) {
                     \* Name of the disk-file which is going to be written in wrt.
                     h := h + 1;
                     goto wrt;
                  } else {
                     \* Another worker beat us to write the next page, thus try again.
                     goto enq;
                  };
            
            (* write page to disk. Intuitively, one would write the
               the page first (wrt) before enqueueing it (enq). However,
               enq determines the file-name of the page.  *)
            wrt: disk := disk \o << h >>;
                 goto deq;
       }
}
***************************************************************************)
\* BEGIN TRANSLATION PCal-657579f916d7a8bbd190c4d63f9c756c
VARIABLES tail, disk, head, history, pc

(* define statement *)
MyProcSet ==                   Workers

ArriveAndAwait(F) == /\ \A p \in MyProcSet : pc[p] \in DOMAIN F
                     /\ pc' = [ p \in MyProcSet |-> F[pc[p]] ]

AAAA == ArriveAndAwait([ m3 |-> "m4", Done |-> "Done" , awtwtA |-> "awtwtB" ])
AAAB == ArriveAndAwait([ m5 |-> "m0", Done |-> "Done" , awtwtB |-> "deq" ])


TotalWork == Len(history) <= Pages




WSafety ==
        /\ IsInjective([ i \in 1..Len(history) |-> history[i][2] ])
        /\ IsInjective(disk)
        /\ (\A p \in MyProcSet : pc[p] = "Done") => \/ tail = VIOLATION
                                                    \/ /\ tail = FINISH
                                                       /\ disk = <<>>


WLiveness == /\ \A w \in MyProcSet: pc[w] = "Done" => \/ tail = VIOLATION
                                                      \/ /\ <>(tail = Pages /\ head = Pages)
                                                         /\ <>[](tail = FINISH)






WLiveness2 == /\ <>[](\/ (tail = FINISH /\ Range(history) = 1..Pages)
                      \/ (tail = VIOLATION /\ Range(history) \subseteq 1..Pages))

VARIABLES result, t, h

vars == << tail, disk, head, history, pc, result, t, h >>

ProcSet == (Workers)

Init == (* Global variables *)
        /\ tail = 0
        /\ disk \in Disks
        /\ head = Max(disk)
        /\ history = <<>>
        (* Process worker *)
        /\ result = [self \in Workers |-> FALSE]
        /\ t = [self \in Workers |-> 0]
        /\ h = [self \in Workers |-> 0]
        /\ pc = [self \in ProcSet |-> "deq"]

deq(self) == /\ pc[self] = "deq"
             /\ t' = [t EXCEPT ![self] = tail]
             /\ IF t'[self] = VIOLATION
                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                   ELSE /\ IF t'[self] = FINISH
                              THEN /\ Assert(disk = <<>>, 
                                             "Failure of assertion at line 278, column 20.")
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
            /\ IF t[self] \notin Range(disk)
                  THEN /\ pc' = [pc EXCEPT ![self] = "wt1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "rd"]
            /\ UNCHANGED << tail, disk, head, history, result, t, h >>

wt1(self) == /\ pc[self] = "wt1"
             /\ IF tail = VIOLATION
                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                   ELSE /\ IF tail = FINISH
                              THEN /\ Assert(disk = <<>>, 
                                             "Failure of assertion at line 309, column 24.")
                                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                              ELSE /\ IF tail = Cardinality(Workers) + head
                                         THEN /\ pc' = [pc EXCEPT ![self] = "casB"]
                                         ELSE /\ TRUE
                                              /\ pc' = [pc EXCEPT ![self] = "wt"]
             /\ UNCHANGED << tail, disk, head, history, result, t, h >>

casB(self) == /\ pc[self] = "casB"
              /\ IF tail = t[self]
                    THEN /\ tail' = FINISH
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ tail' = tail
              /\ IF result'[self]
                    THEN /\ Assert(disk = <<>>, 
                                   "Failure of assertion at line 316, column 33.")
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "wt"]
              /\ UNCHANGED << disk, head, history, t, h >>

rd(self) == /\ pc[self] = "rd"
            /\ Assert(t[self] \in Range(disk), 
                      "Failure of assertion at line 327, column 18.")
            /\ disk' = Remove(disk, t[self])
            /\ pc' = [pc EXCEPT ![self] = "exp"]
            /\ UNCHANGED << tail, head, history, result, t, h >>

exp(self) == /\ pc[self] = "exp"
             /\ history' = history \o << <<self, t[self]>> >>
             /\ \/ /\ pc' = [pc EXCEPT ![self] = "enq"]
                \/ /\ pc' = [pc EXCEPT ![self] = "deq"]
                \/ /\ pc' = [pc EXCEPT ![self] = "casC"]
             /\ UNCHANGED << tail, disk, head, result, t, h >>

casC(self) == /\ pc[self] = "casC"
              /\ IF tail = t[self]
                    THEN /\ tail' = VIOLATION
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ tail' = tail
              /\ IF result'[self]
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "retry"]
              /\ UNCHANGED << disk, head, history, t, h >>

retry(self) == /\ pc[self] = "retry"
               /\ t' = [t EXCEPT ![self] = tail]
               /\ pc' = [pc EXCEPT ![self] = "casC"]
               /\ UNCHANGED << tail, disk, head, history, result, h >>

enq(self) == /\ pc[self] = "enq"
             /\ h' = [h EXCEPT ![self] = head]
             /\ pc' = [pc EXCEPT ![self] = "enq2"]
             /\ UNCHANGED << tail, disk, head, history, result, t >>

enq2(self) == /\ pc[self] = "enq2"
              /\ IF head = h[self]
                    THEN /\ head' = h[self] + 1
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ head' = head
              /\ IF result'[self]
                    THEN /\ h' = [h EXCEPT ![self] = h[self] + 1]
                         /\ pc' = [pc EXCEPT ![self] = "wrt"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "enq"]
                         /\ h' = h
              /\ UNCHANGED << tail, disk, history, t >>

wrt(self) == /\ pc[self] = "wrt"
             /\ disk' = disk \o << h[self] >>
             /\ pc' = [pc EXCEPT ![self] = "deq"]
             /\ UNCHANGED << tail, head, history, result, t, h >>

worker(self) == deq(self) \/ casA(self) \/ wt(self) \/ wt1(self)
                   \/ casB(self) \/ rd(self) \/ exp(self) \/ casC(self)
                   \/ retry(self) \/ enq(self) \/ enq2(self) \/ wrt(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Workers: worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Workers : WF_vars(worker(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION TLA-0c78bfffa3d3b2183c1c2118aaa8586f
-----------------------------------------------------------------------------

=============================================================================
