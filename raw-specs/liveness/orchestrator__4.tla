target: specs/liveness/4/orchestrator.tla
!!!
!tlacli check % --prop Liveness
!!!

---- MODULE orchestrator__4 ----
EXTENDS Integers, TLC, FiniteSets

Servers == {"s1", "s2"}

(*--algorithm threads
variables 
  online = Servers;

define
  Invariant == \E s \in Servers: s \in online
  Safety == \E s \in Servers: [](s \in online)
  \* It's ot the case that all servers are always online
  Liveness == ~[](online = Servers)
end define;

fair process orchestrator = "orchestrator"
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a09a3e434944fdf90dd9ab5c67655673
VARIABLE online

(* define statement *)
Invariant == \E s \in Servers: s \in online
Safety == \E s \in Servers: [](s \in online)

Liveness == ~[](online = Servers)


vars == << online >>

ProcSet == {"orchestrator"}

Init == (* Global variables *)
        /\ online = Servers

orchestrator == \E s \in Servers:
                  \/ /\ s \notin online
                     /\ online' = (online \cup {s})
                  \/ /\ s \in online
                     /\ Cardinality(online) > 1
                     /\ online' = online \ {s}

Next == orchestrator

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(orchestrator)

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5ed9b2eafc0165fc37870965115170dc
====
