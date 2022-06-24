target: specs/topics/trace.tla
!!!
LoadLocal !tlacli check % --inv xyleq10
!!!

---- MODULE trace ----

EXTENDS Integers, TLC

(*--algorithm errortrace
variable x=0; y=0; i=0;

define
  xyleq10 == x * y <= 10
end define;

process incX = "incX"
begin
  EtX:
    while i < 8 do
      x := x + 1;
      i := i + 1;
    end while;
end process;

process incY = "incY"
begin
  EtY:
    while i < 8 do
      y := y + 1;
      i := i + 1;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f6c62dbd6ea368e59153033ccbe27c4d
VARIABLES x, y, i, pc

(* define statement *)
xyleq10 == x * y <= 10


vars == << x, y, i, pc >>

ProcSet == {"incX"} \cup {"incY"}

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ i = 0
        /\ pc = [self \in ProcSet |-> CASE self = "incX" -> "EtX"
                                        [] self = "incY" -> "EtY"]

EtX == /\ pc["incX"] = "EtX"
       /\ IF i < 8
             THEN /\ x' = x + 1
                  /\ i' = i + 1
                  /\ pc' = [pc EXCEPT !["incX"] = "EtX"]
             ELSE /\ pc' = [pc EXCEPT !["incX"] = "Done"]
                  /\ UNCHANGED << x, i >>
       /\ y' = y

incX == EtX

EtY == /\ pc["incY"] = "EtY"
       /\ IF i < 8
             THEN /\ y' = y + 1
                  /\ i' = i + 1
                  /\ pc' = [pc EXCEPT !["incY"] = "EtY"]
             ELSE /\ pc' = [pc EXCEPT !["incY"] = "Done"]
                  /\ UNCHANGED << y, i >>
       /\ x' = x

incY == EtY

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == incX \/ incY
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-1169b976252d1d577d2296f7b97c542e


====

