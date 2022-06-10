target: specs/pluscal.tla
states:
  basic_pluscal:
    config: 1
    states: 4
    distinct: 3

!!!
---- MODULE basic_pluscal ----
EXTENDS Integers, TLC

(* --algorithm pluscal
variables
 x = 2;
 y = TRUE;

begin
  A:
    x := x + 1;
  B:
    x := x + 1;
    y := FALSE;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-260fe5615258a5c7a244901a0ea0501b
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = 2
        /\ y = TRUE
        /\ pc = "A"

A == /\ pc = "A"
     /\ x' = x + 1
     /\ pc' = "B"
     /\ y' = y

B == /\ pc = "B"
     /\ x' = x + 1
     /\ y' = FALSE
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A \/ B
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-471993d4fcb5f472210c7e24b5b87998
====
