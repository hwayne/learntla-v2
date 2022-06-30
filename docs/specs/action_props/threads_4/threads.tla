---- MODULE threads ----
EXTENDS TLC, Integers
CONSTANT NULL

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
  counter = 0;
  lock = NULL;

define
  CounterOnlyIncreases ==
    [][counter' >= counter]_counter

  LockCantBeStolen ==
    [][lock # NULL => lock' = NULL]_lock
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

