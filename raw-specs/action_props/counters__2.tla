target: specs/action_props/counters_2/counters.tla
!!!
LoadLocal !tlacli check % --prop CounterOnlyIncreases
!!!
---- MODULE counters__2 ----
EXTENDS Integers

Counters == {1, 2}
(* --algorithm counters
variables 
  values = [i \in Counters |-> 0];

define
  CounterOnlyIncreases == 
      \A c \in Counters:
        [][values[c]' >= values[c]]_values[c]
end define;  

macro increment() begin
  values[self] := values[self] + 1;
end macro

process counter \in Counters
begin
  A:
    increment();
  B:
    increment();
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-0a87a489656d70a354162f3758aa9099
VARIABLES values, pc

(* define statement *)
CounterOnlyIncreases ==
    \A c \in Counters:
      [][values[c]' >= values[c]]_values[c]


vars == << values, pc >>

ProcSet == (Counters)

Init == (* Global variables *)
        /\ values = [i \in Counters |-> 0]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ values' = [values EXCEPT ![self] = values[self] + 1]
           /\ pc' = [pc EXCEPT ![self] = "B"]

B(self) == /\ pc[self] = "B"
           /\ values' = [values EXCEPT ![self] = values[self] + 1]
           /\ pc' = [pc EXCEPT ![self] = "Done"]

counter(self) == A(self) \/ B(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Counters: counter(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-716722940ef7c3132a96591d8c129442
=====
