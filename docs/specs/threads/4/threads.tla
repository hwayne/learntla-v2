---- MODULE threads ----
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
====
