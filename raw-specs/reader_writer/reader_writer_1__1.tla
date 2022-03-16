target: specs/reader_writer/1/reader_writer.tla
states:
  rw_1:
    states: 3
    distinct: 2
!!!
!tlacli check %
!tlacli translate %
!!!

---- MODULE reader_writer_1__1 ----
EXTENDS Integers, Sequences, TLC

(*--algorithm reader_writer
variables
  queue = <<>>;
  total = 0;

process writer = 1
begin
  AddToQueue:
    queue := Append(queue, 1);
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-15f68acfb561d15918083dc136b7b8b9
VARIABLES queue, total, pc

vars == << queue, total, pc >>

ProcSet == {1}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        /\ pc = [self \in ProcSet |-> "AddToQueue"]

AddToQueue == /\ pc[1] = "AddToQueue"
              /\ queue' = Append(queue, 1)
              /\ pc' = [pc EXCEPT ![1] = "Done"]
              /\ total' = total

writer == AddToQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-7ff5ddfeb2282b8689825e2404cf6c5c
====
