
---- MODULE rw_many__4 ----
EXTENDS Integers, Sequences, TLC

Writers == {1, 2, 3}
Readers = {-1, 0}

(*--algorithm reader_writer
variables
  queue = <<>>;
  total = [r \in Readers |-> 0];

process writer \in Writers
begin
  AddToQueue:
    queue := Append(queue, );
end process;

process reader \in Readers
\* Make this use a local variable so there's no deadlock
begin
  ReadFromQueue:
    if queue # <<>> then
      total[self] := total[self] + Head(queue);
      queue := Tail(queue);
    end if;
end process;
end algorithm; *)
====
