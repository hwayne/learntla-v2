target: specs/reader_writer/3/reader_writer.tla
states:
  rw_2:
    states: 7
    distinct: 5
!!!
!tlacli check %
!tlacli translate %
!!!

---- MODULE reader_writer_1__3 ----
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
    if queue # <<>> then
      total := total + Head(queue);
      queue := Tail(queue);
    end if;
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-23aed7fe7d4618ee4aae9638060ca9fc
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
                 /\ IF queue # <<>>
                       THEN /\ total' = total + Head(queue)
                            /\ queue' = Tail(queue)
                       ELSE /\ TRUE
                            /\ UNCHANGED << queue, total >>
                 /\ pc' = [pc EXCEPT ![2] = "Done"]

reader == ReadFromQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer \/ reader
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a87b547f63310cdf64a3c60ac693219c
====
