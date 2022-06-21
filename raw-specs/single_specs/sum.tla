!!!
target: specs/advanced_operators/sum.tla
!!!
LoadLocal !tlacli check % --inv IsCorrect --const S "{1, 2, 3}"
!!!
RECURSIVE SumSeq(_)

SumSeq(s) == IF s = <<>> THEN 0 ELSE
  Head(s) + SumSeq(Tail(s)) 

SumSeq(s) == 0 \* ???
!!!

---- MODULE sum ----
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT S
ASSUME S \subseteq Int

SumSeq(s) == 0 \* ???

(*--algorithm dup
variable 
  seq \in [1..5 -> S];
  sum = 0;
  i = 1;

define
  TypeInvariant ==
    /\ sum \in Int
    /\ i \in 1..Len(seq)+1

  IsCorrect == pc = "Done" => sum = SumSeq(seq)
end define; 

macro add(x, val) begin
  x := x + val
end macro;

begin
  Iterate:
    while i <= Len(seq) do
      add(sum, seq[i]);
      add(i, 1);
    end while;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-882cba4b5b04a88edcab4aa4448c972a
VARIABLES seq, sum, i, pc

(* define statement *)
TypeInvariant ==
  /\ sum \in Int
  /\ i \in 1..Len(seq)+1


IsCorrect == pc = "Done" => sum = SumSeq(seq)


vars == << seq, sum, i, pc >>

Init == (* Global variables *)
        /\ seq \in [1..5 -> S]
        /\ sum = 0
        /\ i = 1
        /\ pc = "Iterate"

Iterate == /\ pc = "Iterate"
           /\ IF i <= Len(seq)
                 THEN /\ sum' = sum + (seq[i])
                      /\ i' = i + 1
                      /\ pc' = "Iterate"
                 ELSE /\ pc' = "Done"
                      /\ UNCHANGED << sum, i >>
           /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-35ce8d8d851fcf18fa0e9282bedd926f
====
