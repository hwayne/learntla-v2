---- MODULE reports ----
EXTENDS TLC \* For @@
VARIABLE state

States == {
  "LogOut", 
  "LogIn", "Main", "Settings", 
    "Reports", "Report1", "Report2"
}

TopDown == [LogIn |-> {"Main", "Settings", "Reports"}, 
              Reports |-> {"Report1", "Report2"}] @@ [s \in States |-> {}]
              \* @@ is function left-merge        ^^

BottomUp == [Report1 |-> "Reports", Report2 |-> "Reports",
           Reports |-> "LogIn", Main |-> "LogIn", Settings |-> "LogIn"]

\* For TopDown we need to make sure that there are no double-parents
ASSUME \A s1, s2 \in States: s1 # s2 => TopDown[s1] \cap TopDown[s2] = {}

RECURSIVE InTD(_, _)
InTD(s, p) ==
  \/ s = p
  \/ \E c \in TopDown[p]:
    InTD(s, c)

RECURSIVE InBU(_, _)
InBU(s, p) ==
  \/ s = p
  \/ \E c \in DOMAIN BottomUp:
      /\ p = BottomUp[c]
      /\ InBU(s, c)

\* Check the two are identical
ASSUME \A s, s2 \in States: InTD(s, s2) <=> InBU(s, s2)

Trans(from, to) ==
  /\ InTD(state, from)
  /\ state' = to

Init == state = "LogOut"

Next ==
  \/ Trans("LogOut", "Main")
  \/ Trans("Main", "Settings")
  \/ Trans("Settings", "Main")
  \/ Trans("LogIn", "LogOut")
  \/ Trans("LogIn", "Report1")
  \/ Trans("Report1", "Report2")
  \/ Trans("Report2", "Report1")
  \/ Trans("Reports", "Main")

Spec == Init /\ [][Next]_state
AlwaysInLeaf == TopDown[state] = {}
====
