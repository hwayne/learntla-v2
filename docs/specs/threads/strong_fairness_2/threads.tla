---- MODULE threads ----
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
