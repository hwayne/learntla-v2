target: specs/liveness/2/orchestrator.tla
!!!
!tlacli check % --inv Invariant
!tlacli check % --prop Safety
!!!
---- MODULE orchestrator__2 ----
EXTENDS Integers, TLC, FiniteSets

Servers == {"s1", "s2"}

(*--algorithm threads
variables 
  online = Servers;

define
  Invariant == \E s \in Servers: s \in online
  Safety == \E s \in Servers: [](s \in online)
end define;

process orchestrator = "orchestrator"
begin
  Change:
    while TRUE do
      with s \in Servers do
       either
          await s \notin online;
          online := online \cup {s};
        or
          await s \in online;
          await Cardinality(online) > 1;
          online := online \ {s};
        end either;
      end with;
    end while;
end process;

end algorithm; *)
====
