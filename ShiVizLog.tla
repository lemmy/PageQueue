^\[\n _TEAction \|-> \[\n(.|\n)*?name \|-> "(?<event>(.)*)"(.|\n)*?Clock \|-> "(?<clock>.*)",\nHost \|-> (?<host>.*),\n disk \|-> (?<disk>.*),\n h \|-> (?<h>.*),\n head \|-> (?<head>.*),\n pc \|-> (?<pc>.*),\n result \|-> (?<result>.*),\n t \|-> (?<t>.*)\n tail \|-> (?<tail>.*)\n\]

----------------------------- MODULE ShiVizLog -----------------------------
\* Open in https://bestchai.bitbucket.io/shiviz/
\*
\* - Filter history from trace in Trace Explorer
\*   (regex not written to handle multiple lines)
\* - Manually delete initial state from trace below
\*   (ShiViz cannot visualize an initial state)

<<
[
 _TEAction |-> [
   position |-> 2,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":0,\"w2\":0,\"w3\":0,\"w4\":1,\"w5\":0}",
Host |-> w4,
 disk |-> 1..10,
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "deq" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "casA" @@ w5 :> "deq"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> FALSE @@ w5 :> FALSE),
 t |-> (w1 :> 0 @@ w2 :> 0 @@ w3 :> 0 @@ w4 :> 0 @@ w5 :> 0),
 tail |-> 0
],
[
 _TEAction |-> [
   position |-> 3,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":0,\"w2\":0,\"w3\":0,\"w4\":1,\"w5\":1}",
Host |-> w5,
 disk |-> 1..10,
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "deq" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "casA" @@ w5 :> "casA"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> FALSE @@ w5 :> FALSE),
 t |-> (w1 :> 0 @@ w2 :> 0 @@ w3 :> 0 @@ w4 :> 0 @@ w5 :> 0),
 tail |-> 0
],
[
 _TEAction |-> [
   position |-> 4,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":0,\"w2\":0,\"w3\":0,\"w4\":2,\"w5\":1}",
Host |-> w4,
 disk |-> 1..10,
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "deq" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "casA"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> FALSE),
 t |-> (w1 :> 0 @@ w2 :> 0 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 0),
 tail |-> 1
],
[
 _TEAction |-> [
   position |-> 5,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":0,\"w2\":0,\"w3\":0,\"w4\":2,\"w5\":2}",
Host |-> w5,
 disk |-> 1..10,
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "deq" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "deq"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> FALSE),
 t |-> (w1 :> 0 @@ w2 :> 0 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 0),
 tail |-> 1
],
[
 _TEAction |-> [
   position |-> 6,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":1,\"w2\":0,\"w3\":0,\"w4\":2,\"w5\":2}",
Host |-> w1,
 disk |-> 1..10,
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "casA" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "deq"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> FALSE),
 t |-> (w1 :> 1 @@ w2 :> 0 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 0),
 tail |-> 1
],
[
 _TEAction |-> [
   position |-> 7,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":2,\"w2\":0,\"w3\":0,\"w4\":2,\"w5\":2}",
Host |-> w1,
 disk |-> 1..10,
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "wt" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "deq"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> FALSE),
 t |-> (w1 :> 2 @@ w2 :> 0 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 0),
 tail |-> 2
],
[
 _TEAction |-> [
   position |-> 8,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":2,\"w2\":1,\"w3\":0,\"w4\":2,\"w5\":2}",
Host |-> w2,
 disk |-> 1..10,
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "wt" @@ w2 :> "casA" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "deq"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> FALSE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 0),
 tail |-> 2
],
[
 _TEAction |-> [
   position |-> 9,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":3,\"w2\":1,\"w3\":0,\"w4\":2,\"w5\":2}",
Host |-> w1,
 disk |-> 1..10,
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "rd" @@ w2 :> "casA" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "deq"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> FALSE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 0),
 tail |-> 2
],
[
 _TEAction |-> [
   position |-> 10,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":3,\"w2\":1,\"w3\":0,\"w4\":2,\"w5\":3}",
Host |-> w5,
 disk |-> 1..10,
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "rd" @@ w2 :> "casA" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "casA"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> FALSE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 2),
 tail |-> 2
],
[
 _TEAction |-> [
   position |-> 11,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":4,\"w2\":1,\"w3\":0,\"w4\":2,\"w5\":3}",
Host |-> w1,
 disk |-> {1, 3, 4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "exp" @@ w2 :> "casA" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "casA"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> FALSE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 2),
 tail |-> 2
],
[
 _TEAction |-> [
   position |-> 12,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":4,\"w2\":1,\"w3\":0,\"w4\":2,\"w5\":4}",
Host |-> w5,
 disk |-> {1, 3, 4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "exp" @@ w2 :> "casA" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "wt"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 13,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":4,\"w2\":1,\"w3\":0,\"w4\":2,\"w5\":5}",
Host |-> w5,
 disk |-> {1, 3, 4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "exp" @@ w2 :> "casA" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 14,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":4,\"w2\":2,\"w3\":0,\"w4\":2,\"w5\":5}",
Host |-> w2,
 disk |-> {1, 3, 4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "exp" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 15,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":4,\"w2\":2,\"w3\":0,\"w4\":2,\"w5\":6}",
Host |-> w5,
 disk |-> {1, 4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "exp" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 16,
   name |-> "exp",
   location |-> "line 520, col 14 to line 524, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":5,\"w2\":2,\"w3\":0,\"w4\":2,\"w5\":6}",
Host |-> w1,
 disk |-> {1, 4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "enq" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 17,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":5,\"w2\":2,\"w3\":0,\"w4\":3,\"w5\":6}",
Host |-> w4,
 disk |-> {1, 4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "enq" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "rd" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 18,
   name |-> "enq",
   location |-> "line 526, col 14 to line 535, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":6,\"w2\":2,\"w3\":0,\"w4\":3,\"w5\":6}",
Host |-> w1,
 disk |-> {1, 4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "claim" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "rd" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 19,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":6,\"w2\":2,\"w3\":0,\"w4\":4,\"w5\":6}",
Host |-> w4,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "claim" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "exp" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 20,
   name |-> "exp",
   location |-> "line 520, col 14 to line 524, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":6,\"w2\":2,\"w3\":0,\"w4\":5,\"w5\":6}",
Host |-> w4,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "claim" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "enq" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 21,
   name |-> "claim",
   location |-> "line 537, col 16 to line 541, col 73 of module PageQueue"
 ],
Clock |-> "{\"w1\":7,\"w2\":2,\"w3\":0,\"w4\":5,\"w5\":6}",
Host |-> w1,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> np @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "clm1" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "enq" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 22,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":2,\"w3\":0,\"w4\":5,\"w5\":6}",
Host |-> w1,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "enq" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 23,
   name |-> "exp",
   location |-> "line 520, col 14 to line 524, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":2,\"w3\":0,\"w4\":5,\"w5\":7}",
Host |-> w5,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "enq" @@ w5 :> "enq"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 0 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 24,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":2,\"w3\":1,\"w4\":5,\"w5\":7}",
Host |-> w3,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "casA" @@ w4 :> "enq" @@ w5 :> "enq"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 3 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 25,
   name |-> "enq",
   location |-> "line 526, col 14 to line 535, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":2,\"w3\":1,\"w4\":5,\"w5\":8}",
Host |-> w5,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "casA" @@ w4 :> "enq" @@ w5 :> "claim"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 2 @@ w3 :> 3 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 26,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":3,\"w3\":1,\"w4\":5,\"w5\":8}",
Host |-> w2,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "casA" @@ w4 :> "enq" @@ w5 :> "claim"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 3 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 27,
   name |-> "claim",
   location |-> "line 537, col 16 to line 541, col 73 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":3,\"w3\":1,\"w4\":5,\"w5\":9}",
Host |-> w5,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> np),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "casA" @@ w4 :> "enq" @@ w5 :> "clm1"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 3 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 28,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":3,\"w3\":1,\"w4\":5,\"w5\":10}",
Host |-> w5,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 10),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "casA" @@ w4 :> "enq" @@ w5 :> "clm2"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> FALSE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 3 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 3
],
[
 _TEAction |-> [
   position |-> 29,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":3,\"w3\":2,\"w4\":5,\"w5\":10}",
Host |-> w3,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 10),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "wt" @@ w4 :> "enq" @@ w5 :> "clm2"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 30,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":3,\"w3\":3,\"w4\":5,\"w5\":10}",
Host |-> w3,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 10),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "enq" @@ w5 :> "clm2"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 31,
   name |-> "enq",
   location |-> "line 526, col 14 to line 535, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":3,\"w3\":3,\"w4\":6,\"w5\":10}",
Host |-> w4,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 10),
 head |-> 10,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "claim" @@ w5 :> "clm2"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 32,
   name |-> "clm2",
   location |-> "line 548, col 15 to line 560, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":3,\"w3\":3,\"w4\":6,\"w5\":11}",
Host |-> w5,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "claim" @@ w5 :> "deq"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 33,
   name |-> "claim",
   location |-> "line 537, col 16 to line 541, col 73 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":3,\"w3\":3,\"w4\":7,\"w5\":11}",
Host |-> w4,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "clm1" @@ w5 :> "deq"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 34,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":4,\"w3\":3,\"w4\":7,\"w5\":11}",
Host |-> w2,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "rd" @@ w4 :> "clm1" @@ w5 :> "deq"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 3),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 35,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":4,\"w3\":3,\"w4\":7,\"w5\":12}",
Host |-> w5,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "rd" @@ w4 :> "clm1" @@ w5 :> "casA"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 3 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 4),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 36,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":5,\"w3\":3,\"w4\":7,\"w5\":12}",
Host |-> w2,
 disk |-> {4, 5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "clm1" @@ w5 :> "casA"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 4),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 37,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":8,\"w2\":5,\"w3\":4,\"w4\":7,\"w5\":12}",
Host |-> w3,
 disk |-> {5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "exp" @@ w4 :> "clm1" @@ w5 :> "casA"),
 result |-> (w1 :> TRUE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 4),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 38,
   name |-> "clm2",
   location |-> "line 548, col 15 to line 560, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":9,\"w2\":5,\"w3\":4,\"w4\":7,\"w5\":12}",
Host |-> w1,
 disk |-> {5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "exp" @@ w4 :> "clm1" @@ w5 :> "casA"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 4),
 tail |-> 4
],
[
 _TEAction |-> [
   position |-> 39,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":9,\"w2\":5,\"w3\":4,\"w4\":7,\"w5\":13}",
Host |-> w5,
 disk |-> {5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "exp" @@ w4 :> "clm1" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 40,
   name |-> "exp",
   location |-> "line 520, col 14 to line 524, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":9,\"w2\":5,\"w3\":5,\"w4\":7,\"w5\":13}",
Host |-> w3,
 disk |-> {5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "enq" @@ w4 :> "clm1" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 41,
   name |-> "enq",
   location |-> "line 526, col 14 to line 535, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":9,\"w2\":5,\"w3\":6,\"w4\":7,\"w5\":13}",
Host |-> w3,
 disk |-> {5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "claim" @@ w4 :> "clm1" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 42,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":9,\"w2\":5,\"w3\":6,\"w4\":8,\"w5\":13}",
Host |-> w4,
 disk |-> {5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> 11 @@ w5 :> 11),
 head |-> 11,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "claim" @@ w4 :> "clm2" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 43,
   name |-> "clm2",
   location |-> "line 548, col 15 to line 560, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":9,\"w2\":5,\"w3\":6,\"w4\":9,\"w5\":13}",
Host |-> w4,
 disk |-> {5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> 12 @@ w5 :> 11),
 head |-> 12,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "claim" @@ w4 :> "wrt" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 44,
   name |-> "claim",
   location |-> "line 537, col 16 to line 541, col 73 of module PageQueue"
 ],
Clock |-> "{\"w1\":9,\"w2\":5,\"w3\":7,\"w4\":9,\"w5\":13}",
Host |-> w3,
 disk |-> {5, 6, 7, 8, 9, 10},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> 12 @@ w5 :> 11),
 head |-> 12,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "clm1" @@ w4 :> "wrt" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 45,
   name |-> "wrt",
   location |-> "line 562, col 14 to line 568, col 53 of module PageQueue"
 ],
Clock |-> "{\"w1\":9,\"w2\":5,\"w3\":7,\"w4\":10,\"w5\":13}",
Host |-> w4,
 disk |-> {5, 6, 7, 8, 9, 10, 12},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 12,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "clm1" @@ w4 :> "deq" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 46,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":9,\"w2\":5,\"w3\":8,\"w4\":10,\"w5\":13}",
Host |-> w3,
 disk |-> {5, 6, 7, 8, 9, 10, 12},
 h |-> (w1 :> 10 @@ w2 :> np @@ w3 :> 12 @@ w4 :> np @@ w5 :> 11),
 head |-> 12,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "clm2" @@ w4 :> "deq" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 47,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":5,\"w3\":8,\"w4\":10,\"w5\":13}",
Host |-> w1,
 disk |-> {5, 6, 7, 8, 9, 10, 12},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> 12 @@ w4 :> np @@ w5 :> 11),
 head |-> 12,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "clm2" @@ w4 :> "deq" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 48,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":5,\"w3\":8,\"w4\":10,\"w5\":14}",
Host |-> w5,
 disk |-> {5, 6, 7, 8, 9, 10, 12},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> 12 @@ w4 :> np @@ w5 :> 11),
 head |-> 12,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "clm2" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 49,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":6,\"w3\":8,\"w4\":10,\"w5\":14}",
Host |-> w2,
 disk |-> {5, 6, 7, 8, 9, 10, 12},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> 12 @@ w4 :> np @@ w5 :> 11),
 head |-> 12,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "clm2" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 50,
   name |-> "clm2",
   location |-> "line 548, col 15 to line 560, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":6,\"w3\":9,\"w4\":10,\"w5\":14}",
Host |-> w3,
 disk |-> {5, 6, 7, 8, 9, 10, 12},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> 13 @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "wrt" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 1 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 51,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":6,\"w3\":9,\"w4\":11,\"w5\":14}",
Host |-> w4,
 disk |-> {5, 6, 7, 8, 9, 10, 12},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> 13 @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "wrt" @@ w4 :> "casA" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 5 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 52,
   name |-> "wrt",
   location |-> "line 562, col 14 to line 568, col 53 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":6,\"w3\":10,\"w4\":11,\"w5\":14}",
Host |-> w3,
 disk |-> {5, 6, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "deq" @@ w3 :> "deq" @@ w4 :> "casA" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 4 @@ w3 :> 4 @@ w4 :> 5 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 53,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":10,\"w4\":11,\"w5\":14}",
Host |-> w2,
 disk |-> {5, 6, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "deq" @@ w4 :> "casA" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 4 @@ w4 :> 5 @@ w5 :> 5),
 tail |-> 5
],
[
 _TEAction |-> [
   position |-> 54,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":10,\"w4\":12,\"w5\":14}",
Host |-> w4,
 disk |-> {5, 6, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 4 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 6
],
[
 _TEAction |-> [
   position |-> 55,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":11,\"w4\":12,\"w5\":14}",
Host |-> w3,
 disk |-> {5, 6, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "casA" @@ w4 :> "wt" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 6 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 6
],
[
 _TEAction |-> [
   position |-> 56,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":11,\"w4\":13,\"w5\":14}",
Host |-> w4,
 disk |-> {5, 6, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "casA" @@ w4 :> "rd" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 6 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 6
],
[
 _TEAction |-> [
   position |-> 57,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":12,\"w4\":13,\"w5\":14}",
Host |-> w3,
 disk |-> {5, 6, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "wt" @@ w4 :> "rd" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 58,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":12,\"w4\":14,\"w5\":14}",
Host |-> w4,
 disk |-> {5, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "wt" @@ w4 :> "exp" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 59,
   name |-> "exp",
   location |-> "line 520, col 14 to line 524, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":12,\"w4\":15,\"w5\":14}",
Host |-> w4,
 disk |-> {5, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "wt" @@ w4 :> "enq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 60,
   name |-> "enq",
   location |-> "line 526, col 14 to line 535, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":12,\"w4\":16,\"w5\":14}",
Host |-> w4,
 disk |-> {5, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "wt" @@ w4 :> "claim" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 61,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":13,\"w4\":16,\"w5\":14}",
Host |-> w3,
 disk |-> {5, 7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "claim" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 62,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":10,\"w2\":7,\"w3\":13,\"w4\":16,\"w5\":15}",
Host |-> w5,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm2" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "claim" @@ w5 :> "exp"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 63,
   name |-> "clm2",
   location |-> "line 548, col 15 to line 560, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":7,\"w3\":13,\"w4\":16,\"w5\":15}",
Host |-> w1,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "claim" @@ w5 :> "exp"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 64,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":8,\"w3\":13,\"w4\":16,\"w5\":15}",
Host |-> w2,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm1" @@ w2 :> "deq" @@ w3 :> "rd" @@ w4 :> "claim" @@ w5 :> "exp"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 65,
   name |-> "exp",
   location |-> "line 520, col 14 to line 524, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":8,\"w3\":13,\"w4\":16,\"w5\":16}",
Host |-> w5,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm1" @@ w2 :> "deq" @@ w3 :> "rd" @@ w4 :> "claim" @@ w5 :> "enq"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 66,
   name |-> "claim",
   location |-> "line 537, col 16 to line 541, col 73 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":8,\"w3\":13,\"w4\":17,\"w5\":16}",
Host |-> w4,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm1" @@ w2 :> "deq" @@ w3 :> "rd" @@ w4 :> "clm1" @@ w5 :> "enq"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 67,
   name |-> "enq",
   location |-> "line 526, col 14 to line 535, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":8,\"w3\":13,\"w4\":17,\"w5\":17}",
Host |-> w5,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm1" @@ w2 :> "deq" @@ w3 :> "rd" @@ w4 :> "clm1" @@ w5 :> "deq"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 5 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 68,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":9,\"w3\":13,\"w4\":17,\"w5\":17}",
Host |-> w2,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "clm1" @@ w5 :> "deq"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 7 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 69,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":9,\"w3\":13,\"w4\":18,\"w5\":17}",
Host |-> w4,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> 13 @@ w5 :> 11),
 head |-> 13,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "clm2" @@ w5 :> "deq"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 7 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 70,
   name |-> "clm2",
   location |-> "line 548, col 15 to line 560, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":9,\"w3\":13,\"w4\":19,\"w5\":17}",
Host |-> w4,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> 14 @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "casA" @@ w3 :> "rd" @@ w4 :> "wrt" @@ w5 :> "deq"),
 result |-> (w1 :> FALSE @@ w2 :> FALSE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 7 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 7
],
[
 _TEAction |-> [
   position |-> 71,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":10,\"w3\":13,\"w4\":19,\"w5\":17}",
Host |-> w2,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> 14 @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "wt" @@ w3 :> "rd" @@ w4 :> "wrt" @@ w5 :> "deq"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 5),
 tail |-> 8
],
[
 _TEAction |-> [
   position |-> 72,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":10,\"w3\":13,\"w4\":19,\"w5\":18}",
Host |-> w5,
 disk |-> {7, 8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> 14 @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "wt" @@ w3 :> "rd" @@ w4 :> "wrt" @@ w5 :> "casA"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 8),
 tail |-> 8
],
[
 _TEAction |-> [
   position |-> 73,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":10,\"w3\":14,\"w4\":19,\"w5\":18}",
Host |-> w3,
 disk |-> {8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> 14 @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "wt" @@ w3 :> "exp" @@ w4 :> "wrt" @@ w5 :> "casA"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 8),
 tail |-> 8
],
[
 _TEAction |-> [
   position |-> 74,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":10,\"w3\":14,\"w4\":19,\"w5\":19}",
Host |-> w5,
 disk |-> {8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> 14 @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "wt" @@ w3 :> "exp" @@ w4 :> "wrt" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 75,
   name |-> "exp",
   location |-> "line 520, col 14 to line 524, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":10,\"w3\":15,\"w4\":19,\"w5\":19}",
Host |-> w3,
 disk |-> {8, 9, 10, 12, 13},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> 14 @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "wt" @@ w3 :> "enq" @@ w4 :> "wrt" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 76,
   name |-> "wrt",
   location |-> "line 562, col 14 to line 568, col 53 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":10,\"w3\":15,\"w4\":20,\"w5\":19}",
Host |-> w4,
 disk |-> {8, 9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "wt" @@ w3 :> "enq" @@ w4 :> "deq" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 77,
   name |-> "enq",
   location |-> "line 526, col 14 to line 535, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":10,\"w3\":16,\"w4\":20,\"w5\":19}",
Host |-> w3,
 disk |-> {8, 9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "wt" @@ w3 :> "claim" @@ w4 :> "deq" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 78,
   name |-> "claim",
   location |-> "line 537, col 16 to line 541, col 73 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":10,\"w3\":17,\"w4\":20,\"w5\":19}",
Host |-> w3,
 disk |-> {8, 9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "wt" @@ w3 :> "clm1" @@ w4 :> "deq" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 79,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":11,\"w3\":17,\"w4\":20,\"w5\":19}",
Host |-> w2,
 disk |-> {8, 9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "rd" @@ w3 :> "clm1" @@ w4 :> "deq" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 80,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":12,\"w3\":17,\"w4\":20,\"w5\":19}",
Host |-> w2,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "exp" @@ w3 :> "clm1" @@ w4 :> "deq" @@ w5 :> "wt"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 81,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":12,\"w3\":17,\"w4\":20,\"w5\":20}",
Host |-> w5,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "exp" @@ w3 :> "clm1" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 82,
   name |-> "exp",
   location |-> "line 520, col 14 to line 524, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":13,\"w3\":17,\"w4\":20,\"w5\":20}",
Host |-> w2,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "enq" @@ w3 :> "clm1" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 83,
   name |-> "enq",
   location |-> "line 526, col 14 to line 535, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":14,\"w3\":17,\"w4\":20,\"w5\":20}",
Host |-> w2,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> np @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "claim" @@ w3 :> "clm1" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 84,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":14,\"w3\":18,\"w4\":20,\"w5\":20}",
Host |-> w3,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> 14 @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "claim" @@ w3 :> "clm2" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 85,
   name |-> "claim",
   location |-> "line 537, col 16 to line 541, col 73 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":15,\"w3\":18,\"w4\":20,\"w5\":20}",
Host |-> w2,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> 14 @@ w4 :> np @@ w5 :> 11),
 head |-> 14,
 pc |-> (w1 :> "clm1" @@ w2 :> "clm1" @@ w3 :> "clm2" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 86,
   name |-> "clm2",
   location |-> "line 548, col 15 to line 560, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":11,\"w2\":15,\"w3\":19,\"w4\":20,\"w5\":20}",
Host |-> w3,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 12 @@ w2 :> np @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 15,
 pc |-> (w1 :> "clm1" @@ w2 :> "clm1" @@ w3 :> "deq" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 87,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":12,\"w2\":15,\"w3\":19,\"w4\":20,\"w5\":20}",
Host |-> w1,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 15 @@ w2 :> np @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 15,
 pc |-> (w1 :> "clm2" @@ w2 :> "clm1" @@ w3 :> "deq" @@ w4 :> "deq" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 6 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 88,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":12,\"w2\":15,\"w3\":19,\"w4\":21,\"w5\":20}",
Host |-> w4,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 15 @@ w2 :> np @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 15,
 pc |-> (w1 :> "clm2" @@ w2 :> "clm1" @@ w3 :> "deq" @@ w4 :> "casA" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 9 @@ w5 :> 9),
 tail |-> 9
],
[
 _TEAction |-> [
   position |-> 89,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":12,\"w2\":15,\"w3\":19,\"w4\":22,\"w5\":20}",
Host |-> w4,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 15 @@ w2 :> np @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 15,
 pc |-> (w1 :> "clm2" @@ w2 :> "clm1" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "rd"),
 result |-> (w1 :> FALSE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 10
],
[
 _TEAction |-> [
   position |-> 90,
   name |-> "clm2",
   location |-> "line 548, col 15 to line 560, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":13,\"w2\":15,\"w3\":19,\"w4\":22,\"w5\":20}",
Host |-> w1,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 16 @@ w2 :> np @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 16,
 pc |-> (w1 :> "wrt" @@ w2 :> "clm1" @@ w3 :> "deq" @@ w4 :> "wt" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 7 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 10
],
[
 _TEAction |-> [
   position |-> 91,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":13,\"w2\":15,\"w3\":20,\"w4\":22,\"w5\":20}",
Host |-> w3,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 16 @@ w2 :> np @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 16,
 pc |-> (w1 :> "wrt" @@ w2 :> "clm1" @@ w3 :> "casA" @@ w4 :> "wt" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 10 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 10
],
[
 _TEAction |-> [
   position |-> 92,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":13,\"w2\":15,\"w3\":21,\"w4\":22,\"w5\":20}",
Host |-> w3,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 16 @@ w2 :> np @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 16,
 pc |-> (w1 :> "wrt" @@ w2 :> "clm1" @@ w3 :> "wt" @@ w4 :> "wt" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 93,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":13,\"w2\":16,\"w3\":21,\"w4\":22,\"w5\":20}",
Host |-> w2,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 16 @@ w2 :> 16 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 16,
 pc |-> (w1 :> "wrt" @@ w2 :> "clm2" @@ w3 :> "wt" @@ w4 :> "wt" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 94,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":13,\"w2\":16,\"w3\":21,\"w4\":23,\"w5\":20}",
Host |-> w4,
 disk |-> {9, 10, 12, 13, 14},
 h |-> (w1 :> 16 @@ w2 :> 16 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 16,
 pc |-> (w1 :> "wrt" @@ w2 :> "clm2" @@ w3 :> "wt" @@ w4 :> "rd" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 95,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":13,\"w2\":16,\"w3\":21,\"w4\":24,\"w5\":20}",
Host |-> w4,
 disk |-> {9, 12, 13, 14},
 h |-> (w1 :> 16 @@ w2 :> 16 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 16,
 pc |-> (w1 :> "wrt" @@ w2 :> "clm2" @@ w3 :> "wt" @@ w4 :> "exp" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 96,
   name |-> "clm2",
   location |-> "line 548, col 15 to line 560, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":13,\"w2\":17,\"w3\":21,\"w4\":24,\"w5\":20}",
Host |-> w2,
 disk |-> {9, 12, 13, 14},
 h |-> (w1 :> 16 @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "wrt" @@ w2 :> "deq" @@ w3 :> "wt" @@ w4 :> "exp" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 97,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":13,\"w2\":17,\"w3\":22,\"w4\":24,\"w5\":20}",
Host |-> w3,
 disk |-> {9, 12, 13, 14},
 h |-> (w1 :> 16 @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "wrt" @@ w2 :> "deq" @@ w3 :> "wt1" @@ w4 :> "exp" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 98,
   name |-> "wrt",
   location |-> "line 562, col 14 to line 568, col 53 of module PageQueue"
 ],
Clock |-> "{\"w1\":14,\"w2\":17,\"w3\":22,\"w4\":24,\"w5\":20}",
Host |-> w1,
 disk |-> {9, 12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "deq" @@ w2 :> "deq" @@ w3 :> "wt1" @@ w4 :> "exp" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 99,
   name |-> "exp",
   location |-> "line 520, col 14 to line 524, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":14,\"w2\":17,\"w3\":22,\"w4\":25,\"w5\":20}",
Host |-> w4,
 disk |-> {9, 12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "deq" @@ w2 :> "deq" @@ w3 :> "wt1" @@ w4 :> "enq" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 100,
   name |-> "wt1",
   location |-> "line 473, col 14 to line 497, col 53 of module PageQueue"
 ],
Clock |-> "{\"w1\":14,\"w2\":17,\"w3\":23,\"w4\":25,\"w5\":20}",
Host |-> w3,
 disk |-> {9, 12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "deq" @@ w2 :> "deq" @@ w3 :> "wt" @@ w4 :> "enq" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 2 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 101,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":15,\"w2\":17,\"w3\":23,\"w4\":25,\"w5\":20}",
Host |-> w1,
 disk |-> {9, 12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "casA" @@ w2 :> "deq" @@ w3 :> "wt" @@ w4 :> "enq" @@ w5 :> "rd"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 11 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 102,
   name |-> "rd",
   location |-> "line 512, col 13 to line 518, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":15,\"w2\":17,\"w3\":23,\"w4\":25,\"w5\":21}",
Host |-> w5,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "casA" @@ w2 :> "deq" @@ w3 :> "wt" @@ w4 :> "enq" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 11 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 103,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":15,\"w2\":17,\"w3\":24,\"w4\":25,\"w5\":21}",
Host |-> w3,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "casA" @@ w2 :> "deq" @@ w3 :> "wt1" @@ w4 :> "enq" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 11 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 104,
   name |-> "enq",
   location |-> "line 526, col 14 to line 535, col 71 of module PageQueue"
 ],
Clock |-> "{\"w1\":15,\"w2\":17,\"w3\":24,\"w4\":26,\"w5\":21}",
Host |-> w4,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "casA" @@ w2 :> "deq" @@ w3 :> "wt1" @@ w4 :> "claim" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 11 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 105,
   name |-> "wt1",
   location |-> "line 473, col 14 to line 497, col 53 of module PageQueue"
 ],
Clock |-> "{\"w1\":15,\"w2\":17,\"w3\":25,\"w4\":26,\"w5\":21}",
Host |-> w3,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "casA" @@ w2 :> "deq" @@ w3 :> "wt" @@ w4 :> "claim" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 11 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 11
],
[
 _TEAction |-> [
   position |-> 106,
   name |-> "casA",
   location |-> "line 454, col 15 to line 465, col 55 of module PageQueue"
 ],
Clock |-> "{\"w1\":16,\"w2\":17,\"w3\":25,\"w4\":26,\"w5\":21}",
Host |-> w1,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "wt" @@ w2 :> "deq" @@ w3 :> "wt" @@ w4 :> "claim" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 12 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 12
],
[
 _TEAction |-> [
   position |-> 107,
   name |-> "claim",
   location |-> "line 537, col 16 to line 541, col 73 of module PageQueue"
 ],
Clock |-> "{\"w1\":16,\"w2\":17,\"w3\":25,\"w4\":27,\"w5\":21}",
Host |-> w4,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "wt" @@ w2 :> "deq" @@ w3 :> "wt" @@ w4 :> "clm1" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 12 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 12
],
[
 _TEAction |-> [
   position |-> 108,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":17,\"w2\":17,\"w3\":25,\"w4\":27,\"w5\":21}",
Host |-> w1,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "rd" @@ w2 :> "deq" @@ w3 :> "wt" @@ w4 :> "clm1" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 12 @@ w2 :> 8 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 12
],
[
 _TEAction |-> [
   position |-> 109,
   name |-> "deq",
   location |-> "line 443, col 14 to line 452, col 68 of module PageQueue"
 ],
Clock |-> "{\"w1\":17,\"w2\":18,\"w3\":25,\"w4\":27,\"w5\":21}",
Host |-> w2,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> np @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "rd" @@ w2 :> "casA" @@ w3 :> "wt" @@ w4 :> "clm1" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 12 @@ w2 :> 12 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 12
],
[
 _TEAction |-> [
   position |-> 110,
   name |-> "clm1",
   location |-> "line 543, col 15 to line 546, col 69 of module PageQueue"
 ],
Clock |-> "{\"w1\":17,\"w2\":18,\"w3\":25,\"w4\":28,\"w5\":21}",
Host |-> w4,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> 17 @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "rd" @@ w2 :> "casA" @@ w3 :> "wt" @@ w4 :> "clm2" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 12 @@ w2 :> 12 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 12
],
[
 _TEAction |-> [
   position |-> 111,
   name |-> "wt",
   location |-> "line 467, col 13 to line 471, col 70 of module PageQueue"
 ],
Clock |-> "{\"w1\":17,\"w2\":18,\"w3\":26,\"w4\":28,\"w5\":21}",
Host |-> w3,
 disk |-> {12, 13, 14, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> 15 @@ w4 :> 17 @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "rd" @@ w2 :> "casA" @@ w3 :> "wt1" @@ w4 :> "clm2" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 12 @@ w2 :> 12 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 12
],
[
 _TEAction |-> [
   position |-> 112,
   name |-> "wt1",
   location |-> "line 473, col 14 to line 497, col 53 of module PageQueue"
 ],
Clock |-> "{\"w1\":17,\"w2\":18,\"w3\":27,\"w4\":28,\"w5\":21}",
Host |-> w3,
 disk |-> {12, 13, 14, 15, 16},
 h |-> (w1 :> np @@ w2 :> 17 @@ w3 :> np @@ w4 :> 17 @@ w5 :> 11),
 head |-> 17,
 pc |-> (w1 :> "rd" @@ w2 :> "casA" @@ w3 :> "wt" @@ w4 :> "clm2" @@ w5 :> "exp"),
 result |-> (w1 :> TRUE @@ w2 :> TRUE @@ w3 :> TRUE @@ w4 :> TRUE @@ w5 :> TRUE),
 t |-> (w1 :> 12 @@ w2 :> 12 @@ w3 :> 11 @@ w4 :> 10 @@ w5 :> 9),
 tail |-> 12
]
>>
===========================================================================
