target: specs/reader_writer/2/reader_writer.tla
!!!
!tlacli check %
!tlacli translate %
!!!

---- MODULE reader_writer_1__2 ----
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

process reader = 2
begin
  ReadFromQueue:
    total := total + Head(queue);
    queue := Tail(queue);
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f255084c610e664c380e36174d547d3c
VARIABLES queue, total, pc

vars == << queue, total, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "AddToQueue"
                                        [] self = 2 -> "ReadFromQueue"]

AddToQueue == /\ pc[1] = "AddToQueue"
              /\ queue' = Append(queue, 1)
              /\ pc' = [pc EXCEPT ![1] = "Done"]
              /\ total' = total

writer == AddToQueue

ReadFromQueue == /\ pc[2] = "ReadFromQueue"
                 /\ total' = total + Head(queue)
                 /\ queue' = Tail(queue)
                 /\ pc' = [pc EXCEPT ![2] = "Done"]

reader == ReadFromQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer \/ reader
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-d4945c56c0762d6b403322a60248753c
====
