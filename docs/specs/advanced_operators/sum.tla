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
====
