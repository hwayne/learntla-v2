target: specs/threads/3/threads.tla
states:
  threads_3:
    states: 19
    distinct: 17
!!!
LoadLocal !tlacli check % --inv Correct --model-value NULL
!!!
---- MODULE threads__3 ----
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
    lock := NULL; 
end process;
end algorithm; *)
====
