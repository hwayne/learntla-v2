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
    counter := tmp + IF tmp = 0 THEN 1 ELSE -1;
  
  ReleaseLock:
    lock := NULL; 
end process;
end algorithm; *)
====

