---- MODULE optimization ----
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
    await to_process[self] # {};
    with x = CHOOSE x \in to_process[self]: TRUE do
      local := x;
      to_process[self] := @ \ {local};
    end with;
    Update:
      total := total + local;
      goto Read;
end process;

end algorithm; *)
====
