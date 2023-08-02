target: specs/topics/optimization/one_label/optimization.tla
states:
  optimization_one_label:
    states: 2353282
    distinct: 534330
!!!
---- MODULE optimization__5 ----
EXTENDS Integers, Sequences, TLC
CONSTANTS MaxNum, Workers

Constraint == TLCGet("level") < 11
Symmetry == Permutations(Workers)

(*--algorithm alg
variables
  i = 1;
  to_process = [w \in Workers |-> {}];

process writer = "writer"
begin 
  Write:
    while i <= MaxNum do
      with w \in Workers do
        to_process[w] := @ \union {i};
        i := i + 1;
      end with;
    end while;
end process;


process worker \in Workers
variable total = 0;
local = 0;
begin
  Read:
    with x \in to_process[self] do
      total := total + x;
      to_process[self] := @ \ {x};
    end with;
    goto Read;
end process;

end algorithm; *)
====
