target: specs/topics/optimization/view_2/optimization.tla
states:
  optimization_view_2:
    states: 1018176
    distinct: 206964
!!!
---- MODULE optimization_view__2 ----
EXTENDS Integers, Sequences, TLC
CONSTANTS MaxNum, Workers

Constraint == TLCGet("level") < 11
Symmetry == Permutations(Workers)
(*--algorithm alg
variables
  i = 1;
  to_process = [w \in Workers |-> {}];
  aux_last_run = "none";

define
  view == <<i, to_process, pc, total>>
end define;

process writer = "writer"
begin 
  Write:
    while i <= MaxNum do
      with w \in Workers do
        to_process[w] := @ \union {i};
        i := i + 1;
      end with;
      aux_last_run := "writer";
    end while;
end process;

process worker \in Workers
variable total = 0;
local = 0;
begin
  Read:
    with x \in to_process[self] do
      local := x;
      to_process[self] := @ \ {local};
    end with;
    aux_last_run := self;
    Update:
      total := total + local;
      aux_last_run := self;
      goto Read;
end process;

end algorithm; *)
====
