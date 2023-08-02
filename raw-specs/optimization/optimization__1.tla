target: specs/topics/optimization/1/optimization.tla

states:
  optimization_7_3_nosym:
    states: 28351303
    distinct: 8241961
  optimization_7_3_nosym_level:
    states: 872224  
    distinct: 146056
  optimization_6_3:
    states: 3162166
    distinct: 995764
  optimization_7_2:
    states: 1262215
    distinct: 413315
  optimization_7_3_sym:
    states: 4728962
    distinct: 1374882
!!!
---- MODULE optimization__1 ----
EXTENDS Integers, Sequences, TLC
CONSTANTS MaxNum, Workers


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
      local := x;
      to_process[self] := @ \ {local};
    end with;
    Update:
      total := total + local;
      goto Read;
end process;

end algorithm; *)
====
