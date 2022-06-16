target: specs/action_props/threads_1/threads.tla
states:
  threads_3:
    states: 19
    distinct: 17
!!!
LoadLocal !tlacli check % --model NULL
!!! 
---- MODULE threads__1 ----
EXTENDS TLC, Integers
CONSTANT NULL

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
  counter = 0;
  lock = NULL;

define 
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

