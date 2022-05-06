target: specs/threads/liveness_3/threads.tla
states:
  threads_liveness:
    states: 19
    distinct: 17
!!!
!tlacli check % --prop Liveness --model-value NULL
!!!

---- MODULE threads_liveness__3 ----
EXTENDS TLC, Sequences, Integers
CONSTANT NULL

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
  counter = 1;
  lock = NULL;

define
  Liveness ==
    <>(counter = NumThreads)
end define;  

fair process thread \in Threads
variables tmp = 0;
begin
  GetLock:
    await lock = NULL;
    lock := self;

  GetCounter:
    tmp := counter;

  IncCounter:
    counter := tmp + 1;
  
  ReleaseLock:
    lock := NULL; 
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-72af29bbcb42e6407c1d9c03f2b238b8
VARIABLES counter, lock, pc

(* define statement *)
Liveness ==
  <>(counter = NumThreads)

VARIABLE tmp

vars == << counter, lock, pc, tmp >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 1
        /\ lock = NULL
        (* Process thread *)
        /\ tmp = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "GetLock"]

GetLock(self) == /\ pc[self] = "GetLock"
                 /\ lock = NULL
                 /\ lock' = self
                 /\ pc' = [pc EXCEPT ![self] = "GetCounter"]
                 /\ UNCHANGED << counter, tmp >>

GetCounter(self) == /\ pc[self] = "GetCounter"
                    /\ tmp' = [tmp EXCEPT ![self] = counter]
                    /\ pc' = [pc EXCEPT ![self] = "IncCounter"]
                    /\ UNCHANGED << counter, lock >>

IncCounter(self) == /\ pc[self] = "IncCounter"
                    /\ counter' = tmp[self] + 1
                    /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]
                    /\ UNCHANGED << lock, tmp >>

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ lock' = NULL
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << counter, tmp >>

thread(self) == GetLock(self) \/ GetCounter(self) \/ IncCounter(self)
                   \/ ReleaseLock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e41ad837fe5c31a92b71bc1d5a15484f
====
