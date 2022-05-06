target: specs/threads/1/threads.tla
states:
  threads_1:
    states: 6
    distinct: 4
!!!
!tlacli check % --inv Correct
!!!
---- MODULE threads__1 ----
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
begin
  IncCounter:
    counter := counter + 1;
end process;
end algorithm; *)
====
