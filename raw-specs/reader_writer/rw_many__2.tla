target: specs/reader_writer/many_2/reader_writer.tla
states:
  rw_many_2:
    states: 15
    distinct: 8
!!!
---- MODULE rw_many__2 ----
EXTENDS Integers, Sequences, TLC

Writers == {1, 2, 3}

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
\* Make this use a local variable so there's no deadlock
begin
  ReadFromQueue:
    if queue # <<>> then
      total := total + Head(queue);
      queue := Tail(queue);
    end if;
    goto ReadFromQueue;
end process;
end algorithm; *)
====
