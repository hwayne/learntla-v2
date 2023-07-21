target: specs/tla/optimization_fs/optimization.tla
states:
  optimization_fs:
    states: 10794312
    distinct: 3856467
!!!
---- MODULE optimization__4 ----
EXTENDS Integers, Sequences, TLC
CONSTANTS MaxNum, Workers


Constraint == TLCGet("level") < 11

(*--algorithm alg
variables
  to_process \in LET
    i_to_worker == [1..MaxNum -> Workers] \* Map of items to workers
  IN
    { [w \in Workers |->  \* Each worker is mapped to
        {x \in 1..MaxNum: \* the set of items which
        itw[x] = w}]:     \* itw maps to that worker
      itw \in i_to_worker} 

  


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
\* BEGIN TRANSLATION (chksum(pcal) = "fca99fa5" /\ chksum(tla) = "7e9710a6")
VARIABLES to_process, pc, total, local

vars == << to_process, pc, total, local >>

ProcSet == (Workers)

Init == (* Global variables *)
        /\ to_process \in                LET
                            i_to_worker == [1..MaxNum -> Workers]
                          IN
                            { [w \in Workers |->
                                {x \in 1..MaxNum:
                                itw[x] = w}]:
                              itw \in i_to_worker}
        (* Process worker *)
        /\ total = [self \in Workers |-> 0]
        /\ local = [self \in Workers |-> 0]
        /\ pc = [self \in ProcSet |-> "Read"]

Read(self) == /\ pc[self] = "Read"
              /\ \E x \in to_process[self]:
                   /\ local' = [local EXCEPT ![self] = x]
                   /\ to_process' = [to_process EXCEPT ![self] = @ \ {local'[self]}]
              /\ pc' = [pc EXCEPT ![self] = "Update"]
              /\ total' = total

Update(self) == /\ pc[self] = "Update"
                /\ total' = [total EXCEPT ![self] = total[self] + local[self]]
                /\ pc' = [pc EXCEPT ![self] = "Read"]
                /\ UNCHANGED << to_process, local >>

worker(self) == Read(self) \/ Update(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Workers: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
