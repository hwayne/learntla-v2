
---- MODULE dining_philosophers__2 ----
EXTENDS TLC, Sequences, Integers
CONSTANT NP \* Number Philosophers
VARIABLES table, held

vars == <<table, held>>

Forks == 1..NP
P == 1..NP

------
Range(f) == {f[x]: x \in DOMAIN f}
set ++ x == set \union {x}
set -- x == set \ {x}
------

TypeInv ==
  /\ table \subseteq Forks
  /\ held \in [P -> SUBSET Forks]

ForkInv ==
  LET ForkSets == {table, Range(held)} IN
    /\ UNION ForkSets = Forks
    /\ \A s1, s2 \in ForkSets:
      s1 # s2 => s1 \intersect s2 = {}

Left(p) == IF p = 1 THEN NP ELSE p - 1
Right(p) == IF p = NP THEN 1 ELSE p + 1

HeldInv ==
  \A p \in P:
    held[p] \subseteq {Left(p), Right(p)}

Init ==
  /\ table = Forks
  /\ held = [p \in P |-> {}]

Pickup(p, f) ==
  /\ f \in table
  /\ table' = table -- f
  /\ held' = [held EXCEPT ![p] = @ ++ f]

Eat(p) ==
  /\ held[p] = {Left(p), Right(p)}
  /\ table' = table \union held[p]
  /\ held' = [held EXCEPT ![p] = {}]

Philosopher(p) ==
  \/ Pickup(p, Left(p))
  \/ Pickup(p, Right(p))
  \/ Eat(p)

Next ==
  \E p \in P:
    \/ Philosopher(p)

Fairness ==
  \A p \in P:
    WF_vars(Philosopher(p))

Spec == Init /\ [][Next]_vars /\ Fairness
====
