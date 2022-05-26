target: specs/threads/liveness_4/threads.tla
states:
  threads_liveness:
    states: 19
    distinct: 17
!!!
!tlacli check % --prop Liveness --model-value NULL
!!!
---- MODULE threads_liveness__4 ----
EXTENDS TLC, Sequences, Integers
CONSTANT NULL

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
  counter = 1;
  lock = NULL;

define
  Liveness ==
    <>[](counter = NumThreads)
end define;  

fair process thread \in Threads
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
