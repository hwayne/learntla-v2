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
=====
