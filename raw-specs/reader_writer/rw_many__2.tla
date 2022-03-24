target: specs/reader_writer/many_2/reader_writer.tla
states:
  rw_many_2:
    states: 15
    distinct: 8
!!!

---- MODULE rw_many__2 ----
EXTENDS Integers, Sequences, TLC

Writers == {1, 2}

(*--algorithm reader_writer
variables
  queue = <<>>;
  total = 0;

process writer \in Writers
begin
  AddToQueue:
    queue := Append(queue, 1);
end process;

process reader = 0
begin
  ReadFromQueue:
    if queue # <<>> then
      total := total + Head(queue);
      queue := Tail(queue);
    end if;
    goto ReadFromQueue;
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-117d0b288cf4d11ca1986a816d0cba3e
VARIABLES queue, total, pc

vars == << queue, total, pc >>

ProcSet == (Writers) \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "AddToQueue"
                                        [] self = 0 -> "ReadFromQueue"]

AddToQueue(self) == /\ pc[self] = "AddToQueue"
                    /\ queue' = Append(queue, 1)
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ total' = total

writer(self) == AddToQueue(self)

ReadFromQueue == /\ pc[0] = "ReadFromQueue"
                 /\ IF queue # <<>>
                       THEN /\ total' = total + Head(queue)
                            /\ queue' = Tail(queue)
                       ELSE /\ TRUE
                            /\ UNCHANGED << queue, total >>
                 /\ pc' = [pc EXCEPT ![0] = "ReadFromQueue"]

reader == ReadFromQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reader
           \/ (\E self \in Writers: writer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6e7b9da204d6c28fef621f630013b848
====
