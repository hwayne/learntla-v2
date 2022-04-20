target: specs/calculator/3/calculator.tla
!!!
!tlacli check % --const NumInputs 5 --const Target 417 --inv Invariant
!!!
---- MODULE calculator__3 ----
EXTENDS Integers, TLC
CONSTANT NumInputs, Target

Digits == 0..9

(* --algorithm calculator
variables 
  i = 0;
  sum = 0;
define
  Invariant == sum # Target
end define;

begin
  Calculator:
    while i < NumInputs do
      with x \in Digits do
        either
          \* Add
          sum := sum + x;
        or
          \* Subtract
          sum := sum - x;
        or
          \* Multiply
          sum := sum * x;
        end either;
      end with;
      i := i + 1;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a0ab8e853b795b8a0047b2f8e44c7da0
VARIABLES i, sum, pc

(* define statement *)
Invariant == sum # Target


vars == << i, sum, pc >>

Init == (* Global variables *)
        /\ i = 0
        /\ sum = 0
        /\ pc = "Calculator"

Calculator == /\ pc = "Calculator"
              /\ IF i < NumInputs
                    THEN /\ \E x \in Digits:
                              \/ /\ sum' = sum + x
                              \/ /\ sum' = sum - x
                              \/ /\ sum' = sum * x
                         /\ i' = i + 1
                         /\ pc' = "Calculator"
                    ELSE /\ pc' = "Done"
                         /\ UNCHANGED << i, sum >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Calculator
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3f82a03a7b9b4b5e4cdabd4ff4e73e54
====
