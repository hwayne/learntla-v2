target: specs/threads/strong_fairness_2/threads.tla
states:
  strong_fairness:
    states: 15
    distinct: 8
!!!
LoadLocal !tlacli check % --model-value NULL --prop Liveness
!!!
---- MODULE strong_fairness__2 ----
EXTENDS Integers
CONSTANT NULL

Threads == 1..2

(*--algorithm threads
variable lock = NULL;

define
  Liveness == 
    \A t \in Threads:
      <>(lock = t)
end define;

fair+ process thread \in Threads
begin
  GetLock:
    await lock = NULL;
    lock := self;
  ReleaseLock:
    lock := NULL;
  Reset:
    goto GetLock;
end process;
end algorithm; *)
====
