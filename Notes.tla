------------------------------- MODULE Notes -------------------------------
=============================================================================
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

       \* Note YYY
       \* It is acceptable to deviate from strict FIFO (no strict BFS).
       \* Should it be possible to define a bound for the deviation?
       \* At the implementation level, an enqueue operation is not
       \* atomic but consists of atomically (AtomicLong) incrementing
       \* the enqueue counter head and (re-) naming the disk file.  This
       \* can result in interleavings where a disk file for head is
       \* not yet written but a disk file for head + n already is.  A
       \* dequeue opeartion with head thus cannot make progress while
       \* the dequeue for head + n progresses.


           \* Note XXX
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

The algorithm relies on two synchronization primitives:

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
