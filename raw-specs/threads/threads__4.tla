target: specs/threads/4/threads.tla
!!!
LoadLocal !tlacli check % --inv Correct --model-value NULL
LoadLocal !tlacli check % --inv Correct --model-value NULL --inv CounterNotLtTmp --inv TypeInvariant
!!!
  \* Needs to be below translation
  TypeInvariant ==
    /\ counter \in 0..NumThreads
    /\ tmp \in [Threads -> 0..NumThreads]
    /\ lock \in Threads \union {NULL}

  CounterNotLtTmp ==
    tmp \in [Threads -> 0..counter]

  \* or

  CounterNotLtTmp ==
    \A t \in Threads:
      tmp[t] <= counter

!!!
---- MODULE threads__4 ----
EXTENDS TLC, Sequences, Integers
CONSTANT NULL

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
  counter = 0;
  lock = NULL;

define
  AllDone == 
    \A t \in Threads: pc[t] = "Done"

  Correct ==
      AllDone => counter = NumThreads
end define;  

process thread \in Threads
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
    assert lock = self;
    lock := NULL; 
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3435c886b89ef05fefa6d71d557d8ff8
VARIABLES counter, lock, pc

(* define statement *)
AllDone ==
  \A t \in Threads: pc[t] = "Done"

Correct ==
    AllDone => counter = NumThreads

VARIABLE tmp

vars == << counter, lock, pc, tmp >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 0
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
                     /\ Assert(lock = self, 
                               "Failure of assertion at line 41, column 5.")
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

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e6ce0e39c41e30ca69ad70172a9a050d
====
