target: specs/reader_writer/rw_local_2/reader_writer.tla
states:
  rw_local_2:
    states: 15
    distinct: 11
!!!
!tlacli check %
!!!

---- MODULE rw_local__2 ----
EXTENDS Integers, Sequences, TLC

(*--algorithm reader_writer
variables
  queue = <<>>;
  total = 0;

process writer = 1
variables
  i = 0;
begin
  AddToQueue:
    while i < 2 do
      queue := Append(queue, 1);
      i := i + 1;
    end while;
end process;

process reader = 0
begin
  ReadFromQueue:
    if queue # <<>> then
      total := total + Head(queue);
      queue := Tail(queue);
    end if;
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7e9d184a3303e3c9cb3404e566d04e97
VARIABLES queue, total, pc, i

vars == << queue, total, pc, i >>

ProcSet == {1} \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        (* Process writer *)
        /\ i = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "AddToQueue"
                                        [] self = 0 -> "ReadFromQueue"]

AddToQueue == /\ pc[1] = "AddToQueue"
              /\ IF i < 2
                    THEN /\ queue' = Append(queue, 1)
                         /\ i' = i + 1
                         /\ pc' = [pc EXCEPT ![1] = "AddToQueue"]
                    ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                         /\ UNCHANGED << queue, i >>
              /\ total' = total

writer == AddToQueue

ReadFromQueue == /\ pc[0] = "ReadFromQueue"
                 /\ IF queue # <<>>
                       THEN /\ total' = total + Head(queue)
                            /\ queue' = Tail(queue)
                       ELSE /\ TRUE
                            /\ UNCHANGED << queue, total >>
                 /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ i' = i

reader == ReadFromQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer \/ reader
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6282d042bd084f7d56431e6185728e55
====
