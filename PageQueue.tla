----------------------------- MODULE PageQueue -----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Workers, \* The set of Workers
\*         M,J,       \* Main and JMX threads
         Pages    \* The number of total pages to insert into the Queue

ASSUME /\ Workers # {}                      (* at least one worker *)
       /\ Pages \in Nat               (* maximum number of pages to write *)

-----------------------------------------------------------------------------

(***************************************************************************)
(* The image of the function F.                                            *)
(***************************************************************************)
Image(F) == { F[x] : x \in DOMAIN F }

(* The sequence seq with e removed or seq iff e \notin Image(seq) *)
Remove(seq, e) == SelectSeq(seq, LAMBDA s: s # e)

FINISH  == -1
VIOLATION == -2

SUSPEND == -3

-----------------------------------------------------------------------------
(***************************************************************************
--algorithm PageQueue { \* See tlc2.tool.queue.IStateQueue for Java API
       variables idle = 0;
                 tail = 0; \* A strictly monotonic increasing counter
                 head \in 1..Pages; \* A strictly monotonic increasing counter. There is at least a single
                           \* Page available produced by the generation of initial states.
                 disk = [ i \in 1..head |-> i ];
       
       define {
           isDone == head = Pages /\ tail + 1 = Pages
           isAvail == head >= tail
           
           \* When M is in its CS, no worker is making progress (workers are allowed to keep spinning)  
\*           MSafety == pc[M] = "msc" => \A w \in Workers : pc[w] \notin {"exp","enq","inc"}
           
           \* For as long as there is work, head >= tail.
           WSafety == /\ head >= tail
                      /\ (\A p \in (*ProcSet*) Workers : pc[p] = "Done") => \/ tail = VIOLATION
                                                                            \/ /\ tail = FINISH
                                                                               /\ disk = <<>>
           
           (* If a violation is found, it is possible that only a single worker explored states ("exp")
              or *)
           WLiveness == \A w \in Workers: pc[w] = "Done" => \/ tail = VIOLATION
                                                            \/ /\ <>(tail = Pages /\ head = Pages)
                                                               /\ <>[](tail = FINISH)
       }

       (* Called by JMX thread. *)
       macro peek() {
           \* Return full page where JMX can read the first state (or N states) from.
           \* Page deletion can happen asynchronously by a dedicated cleanup thread or
           \* purged by each worker when done with the page. The latter design would
           \* probably cause problems here.
           skip; \* TODO
       }
       
       (* Called by worker threads. *)
       macro finishAll() {
           tail := FINISH;
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

       macro enqueue(worker) {
           \* This is too simple for an actual implementation,
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
           head := head + 1;
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
                 if (expected = FINISH \/ expected = VIOLATION) {
                   goto Done;
\*                 } else if (expected < 0 /\ expected = (Cardinality(Workers) - 1)  * (-1)) {
\*                   (* This is the last unsuspended worker, finish model checking *)
\*                   fns: tail := FINISH;
\*                        goto Done;
\*                 } else if (expected < 0) {
\*                   (* Signal that this worker has suspended. *)
\*                   casB: CAS(result, tail, expected, expected - 1);
\*                         if (result) {
\*                            (* Successfully signaled suspension, now
\*                               await condition to continue work. *)
\*                            await \/ tail = FINISH
\*                                  \/ tail > 0 ; \* Only needed with SUSPEND from main thread. 
\*                            goto deq;
\*                         } else {
\*                            (* Just retry to signal suspension. *)
\*                            goto deq;
\*                         };
                 (* This is a non-atomic comparison. We might read an old value of head here. 
                    Check if work is available and wait otherwise.*)
                 } else if (head = expected) {
                   chk: expected := head;
                        if (idle + 1 = Cardinality(Workers)) {
                            tail := FINISH;
                            goto Done;
                        } else {
                            (*inc:*) idle := idle + 1;
                            spn: while (head = expected /\ tail > 0) {
                               (* busy wait for a state change let it either be
                                  unseen states or global termination. *)
                               wt2: skip;
                            };
                            \*TODO Decrement idle again.
                            idle := idle - 1;
                            goto deq;
                        }
                 } else {
                   \* deq/claim and read a page.
                   casA: CAS(result, tail, expected, expected + 1);
                         if (result) {
                            expected := tail;
                            goto rd;
                         } else {
                           (* CAS can fail for two reasons:
                              a) Another worker dequeued the
                                 page (normal case).
                              b) Model checking finished
                                 In both cases return to deq. *)
                            goto deq;
                         };
                 };

            \* evaluate next-state relation. This a) might
            \* terminate model checking iff a violation is
            \* found, b) no unseen state are found by this
            \* worker, or c) unseen states are found and 
            \* have to be enqueued.
            \* Non-deterministically choose steps.
            rd:  await expected \in Image(disk);
                 disk := Remove(disk, expected);
            exp: either { tail := VIOLATION; goto Done; (* a) *) }
                 or { if (tail > Pages) {
                          goto deq; (* b) *)
                      } else { 
                          skip; (* c) *)
                      };
                    };

            (* enq a page. *)
            enq: head := head + 1;
                 expected := head;
            
            (* write page to disk *)
            wrt: disk := disk \o << expected >>;
                 goto deq;
       }
       
\*       fair process (main = M)
\*          variable x = Pages + 1;
\*       {
\*       
\*           \* In an actual implementation suspendAll only happens infrequently (~once a minute). 
\*           msus:   x := tail || tail := SUSPEND;
\*                   \* TODO Must not enter mcs before all workers are actually suspended. msus
\*                   \* just signals suspension to workers but doesn't wait for all to suspend.
\*           mwt:    await tail = SUSPEND - Cardinality(Workers);        
\*           mcs:    skip; \* Critical section of main
\*           mres:   tail := x;
\*           mcheck: if (tail = FINISH) {
\*              goto Done;
\*           } else {
\*              goto msus;
\*           }           
\*       }
\*       
\*       process (jmx = J) {
\*           \* In an actual implementation peek happens very infrequently (manually requested by user). 
\*           jpk:  peek();
\*           jchk: if (tail = FINISH) {
\*              goto Done;
\*           } else {
\*              goto jpk;
\*           }           
\*       }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES idle, tail, head, disk, pc

(* define statement *)
isDone == head = Pages /\ tail + 1 = Pages
isAvail == head >= tail





WSafety == /\ head >= tail
           /\ (\A p \in             Workers : pc[p] = "Done") => \/ tail = VIOLATION
                                                                 \/ /\ tail = FINISH
                                                                    /\ disk = <<>>



WLiveness == \A w \in Workers: pc[w] = "Done" => \/ tail = VIOLATION
                                                 \/ /\ <>(tail = Pages /\ head = Pages)
                                                    /\ <>[](tail = FINISH)

VARIABLES result, expected

vars == << idle, tail, head, disk, pc, result, expected >>

ProcSet == (Workers)

Init == (* Global variables *)
        /\ idle = 0
        /\ tail = 0
        /\ head \in 1..Pages
        /\ disk = [ i \in 1..head |-> i ]
        (* Process worker *)
        /\ result = [self \in Workers |-> FALSE]
        /\ expected = [self \in Workers |-> 0]
        /\ pc = [self \in ProcSet |-> "deq"]

deq(self) == /\ pc[self] = "deq"
             /\ expected' = [expected EXCEPT ![self] = tail]
             /\ IF expected'[self] = FINISH \/ expected'[self] = VIOLATION
                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                   ELSE /\ IF head = expected'[self]
                              THEN /\ pc' = [pc EXCEPT ![self] = "chk"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "casA"]
             /\ UNCHANGED << idle, tail, head, disk, result >>

chk(self) == /\ pc[self] = "chk"
             /\ expected' = [expected EXCEPT ![self] = head]
             /\ IF idle + 1 = Cardinality(Workers)
                   THEN /\ tail' = FINISH
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ idle' = idle
                   ELSE /\ idle' = idle + 1
                        /\ pc' = [pc EXCEPT ![self] = "spn"]
                        /\ tail' = tail
             /\ UNCHANGED << head, disk, result >>

spn(self) == /\ pc[self] = "spn"
             /\ IF head = expected[self] /\ tail > 0
                   THEN /\ pc' = [pc EXCEPT ![self] = "wt2"]
                        /\ idle' = idle
                   ELSE /\ idle' = idle - 1
                        /\ pc' = [pc EXCEPT ![self] = "deq"]
             /\ UNCHANGED << tail, head, disk, result, expected >>

wt2(self) == /\ pc[self] = "wt2"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "spn"]
             /\ UNCHANGED << idle, tail, head, disk, result, expected >>

casA(self) == /\ pc[self] = "casA"
              /\ IF tail = expected[self]
                    THEN /\ tail' = expected[self] + 1
                         /\ result' = [result EXCEPT ![self] = TRUE]
                    ELSE /\ result' = [result EXCEPT ![self] = FALSE]
                         /\ tail' = tail
              /\ IF result'[self]
                    THEN /\ expected' = [expected EXCEPT ![self] = tail']
                         /\ pc' = [pc EXCEPT ![self] = "rd"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "deq"]
                         /\ UNCHANGED expected
              /\ UNCHANGED << idle, head, disk >>

rd(self) == /\ pc[self] = "rd"
            /\ expected[self] \in Image(disk)
            /\ disk' = Remove(disk, expected[self])
            /\ pc' = [pc EXCEPT ![self] = "exp"]
            /\ UNCHANGED << idle, tail, head, result, expected >>

exp(self) == /\ pc[self] = "exp"
             /\ \/ /\ tail' = VIOLATION
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                \/ /\ IF tail > Pages
                         THEN /\ pc' = [pc EXCEPT ![self] = "deq"]
                         ELSE /\ TRUE
                              /\ pc' = [pc EXCEPT ![self] = "enq"]
                   /\ tail' = tail
             /\ UNCHANGED << idle, head, disk, result, expected >>

enq(self) == /\ pc[self] = "enq"
             /\ head' = head + 1
             /\ expected' = [expected EXCEPT ![self] = head']
             /\ pc' = [pc EXCEPT ![self] = "wrt"]
             /\ UNCHANGED << idle, tail, disk, result >>

wrt(self) == /\ pc[self] = "wrt"
             /\ disk' = disk \o << expected[self] >>
             /\ pc' = [pc EXCEPT ![self] = "deq"]
             /\ UNCHANGED << idle, tail, head, result, expected >>

worker(self) == deq(self) \/ chk(self) \/ spn(self) \/ wt2(self)
                   \/ casA(self) \/ rd(self) \/ exp(self) \/ enq(self)
                   \/ wrt(self)

Next == (\E self \in Workers: worker(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Workers : WF_vars(worker(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------


=============================================================================





















VARIABLES tail, \* A strictly monotonic increasing counter
          head, \* A strictly monotonic increasing counter
          waitset, \* The set of waiting workers
          workers
          
vars == <<tail, head, waitset, workers>>

-----------------------------------------------------------------------------

HasWork == head >= tail

IsDone == head = Pages /\ tail + 1 = Pages

Update(worker, page) == Replace(workers, worker, [id: {worker.id}, state: {IF worker.state = "P" THEN "C" ELSE "P"}, page: {page}])

-----------------------------------------------------------------------------

Enqueue(worker) == /\ worker.state = "P"
                   /\ head' = head + 1 \* make work avaiable (CAS)
                   /\ workers' = Update(worker, head') \* worker's page is assigned id head'
                   /\ UNCHANGED <<tail, waitset>>


Dequeue(worker) == /\ worker.state = "C"
                   /\ HasWork \* work available (CAS)
                   /\ tail' = tail + 1 \* consume work (CAS)
                   /\ workers' = Update(worker, tail)
                   /\ UNCHANGED <<head, waitset>>
                           
DequeueWait(worker) == /\ worker.state = "C"
                       /\ ~HasWork
                       /\ Cardinality(waitset) < Cardinality(workers) - 1 \* Some are waiting
                       /\ Wait(worker, waitset) \* No work available, wait...
                       /\ UNCHANGED <<head, tail, workers>>

DequeueNotify(worker) == /\ worker.state = "C"
                         /\ ~HasWork
                         /\ Cardinality(waitset) = Cardinality(workers) - 1 \* All except worker are waiting
                         /\ UNCHANGED vars

-----------------------------------------------------------------------------

Init == /\ tail = 1
        /\ head = 0
        /\ waitset = {} \* None of the workers is waiting.
        /\ workers = [id: Workers, state: {"P"}, page: {-1}]

Enq == ~IsDone /\ \E w \in (workers \ waitset): Enqueue(w)

Deq == ~IsDone /\ \E w \in (workers \ waitset): Dequeue(w)

DeqWait == ~IsDone /\ \E w \in (workers \ waitset): DequeueWait(w)

DeqEnd ==  ~IsDone /\ \E w \in (workers \ waitset): DequeueNotify(w)

(* Keep scheduling running workers until out of work. *)
Next == Deq \/ Enq \/ DeqWait \/ DeqEnd
-----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

TypeOK == \A worker \in workers: 
              /\ worker.id \in Workers
              /\ worker.page \in Int
              /\ worker.state \in {"P", "C"}

Inv == waitset # Workers \* No deadlock due to all workers waiting.

\*Inv2 == IsDone => \A worker \in workers: worker.state = "C"
=============================================================================
