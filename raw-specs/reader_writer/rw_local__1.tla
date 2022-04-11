target: specs/reader_writer/rw_local_1/reader_writer.tla
states:
  rw_local_1:
    states: 15
    distinct: 11
!!!
!tlacli check %
!!!

---- MODULE rw_local__1 ----
EXTENDS Integers, Sequences, TLC

(*--algorithm reader_writer
variables
  queue = <<>>;
  total = 0;
  i = 0;

process writer = 1
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-0bcd9a8024c1d90ab8a72d4b3cda9ed0
VARIABLES queue, total, i, pc

vars == << queue, total, i, pc >>

ProcSet == {1} \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a78cbc5c7192478d1bdcd76485645600
====
