---- MODULE state_machine ----
VARIABLE state

Trans(a, b) ==
  /\ state = a
  /\ state' = b

Init == state = "BothOff"

Next == 
  \/ Trans("BothOff", "WallOff")
  \/ Trans("BothOff", "LampOff")
  \/ Trans("WallOff", "On")
  \/ Trans("WallOff", "BothOff")
  \/ Trans("LampOff", "BothOff")
  \/ Trans("LampOff", "On")
  \/ Trans("On", "WallOff")
  \/ Trans("On", "LampOff")
  \/ Trans("error", "fetching")

Spec == Init /\ [][Next]_state
====
