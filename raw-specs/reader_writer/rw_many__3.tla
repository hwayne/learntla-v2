
---- MODULE rw_many__3 ----
EXTENDS Integers, Sequences, TLC

Writers == {1, 2, 3}

(*--algorithm reader_writer
variables
  queue = <<>>;
  total = 0;

process writer \in Writers
begin
  AddToQueue:
    queue := Append(queue, self);
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6c5cc353948e03151f1729a313737477
VARIABLES queue, total, pc

vars == << queue, total, pc >>

ProcSet == (Writers) \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "AddToQueue"
                                        [] self = 0 -> "ReadFromQueue"]

AddToQueue(self) == /\ pc[self] = "AddToQueue"
                    /\ queue' = Append(queue, self)
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-70f4be979c13aeb860f1cfe5635132f1
====
