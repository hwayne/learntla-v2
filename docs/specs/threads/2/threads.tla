---- MODULE threads ----
EXTENDS TLC, Sequences, Integers

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
