target: specs/action_props/counters_1/counters.tla
states:
  action_prop_counter:
    states: 14
    distinct: 9
!!!
LoadLocal !tlacli check %
!!!
---- MODULE counters__1 ----
EXTENDS Integers

Counters == {1, 2}
(* --algorithm counters
variables 
  values = [i \in Counters |-> 0];

define
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
