target: specs/topics/optimization/fs/optimization.tla
states:
  optimization_fs:
    states: 10794312
    distinct: 3856467
!!!
---- MODULE optimization__4 ----
EXTENDS Integers, Sequences, TLC
CONSTANTS MaxNum, Workers

Constraint == TLCGet("level") < 11
Symmetry == Permutations(Workers)

(*--algorithm alg
variables
  to_process \in {
    tp \in [Workers -> SUBSET (1..MaxNum)]:
      \A x \in 1..MaxNum:
        \E w \in Workers:
          /\ x \in tp[w]
          /\ \A w2 \in Workers \ {w}:
            x \notin tp[w2]
    }



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
