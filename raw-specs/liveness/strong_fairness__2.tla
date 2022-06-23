target: specs/threads/strong_fairness_2/threads.tla
states:
  strong_fairness_threads:
    states: 15
    distinct: 8
!!!
LoadLocal !tlacli check % --model-value NULL --prop Liveness
!!!
---- MODULE strong_fairness__2 ----
EXTENDS Integers
CONSTANT NULL

Threads == 1..2

(*--algorithm threads
variable lock = NULL;

define
  Liveness == 
    \A t \in Threads:
      <>(lock = t)
end define;

fair+ process thread \in Threads
begin
  GetLock:
    await lock = NULL;
    lock := self;
  ReleaseLock:
    lock := NULL;
  Reset:
    goto GetLock;
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e5bc1fcd763a4b523f4b298df7eaba20
VARIABLES lock, pc

(* define statement *)
Liveness ==
  \A t \in Threads:
    <>(lock = t)


vars == << lock, pc >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ lock = NULL
        /\ pc = [self \in ProcSet |-> "GetLock"]

GetLock(self) == /\ pc[self] = "GetLock"
                 /\ lock = NULL
                 /\ lock' = self
                 /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ lock' = NULL
                     /\ pc' = [pc EXCEPT ![self] = "Reset"]

Reset(self) == /\ pc[self] = "Reset"
               /\ pc' = [pc EXCEPT ![self] = "GetLock"]
               /\ lock' = lock

thread(self) == GetLock(self) \/ ReleaseLock(self) \/ Reset(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : SF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-1207d2abc402476132987aae3fd2ec91
====
