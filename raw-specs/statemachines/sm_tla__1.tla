target: specs/topics/state_machines/lamp/tla/state_machine.tla
!!!
LoadLocal !tlacli check %
!!!

---- MODULE sm_tla__1 ----
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

Spec == Init /\ [][Next]_state
====
