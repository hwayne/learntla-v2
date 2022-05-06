target: specs/threads/2/threads.tla
states:
  threads_2:
    states: 18
    distinct: 13
!!!
!tlacli check % --inv Correct
!!!
---- MODULE threads__2 ----
EXTENDS TLC, Sequences, Integers

\* Hardcoded, in a real spec NumThreads would be a constant
NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
  counter = 0;

define
  AllDone == 
    \A t \in Threads: pc[t] = "Done"

  Correct ==
      AllDone => counter = NumThreads
end define;  

process thread \in Threads
variables tmp = 0;
begin
  GetCounter:
    tmp := counter;

  IncCounter:
    counter := tmp + 1;
end process;
end algorithm; *)
====
