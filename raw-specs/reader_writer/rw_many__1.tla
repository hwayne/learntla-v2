target: specs/reader_writer/rw_many_1/reader_writer.tla
states:
  rw_many_1:
    states: 44
    distinct: 23

!!!
---- MODULE rw_many__1 ----
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
begin
  ReadFromQueue:
    if queue # <<>> then
      total := total + Head(queue);
      queue := Tail(queue);
    end if;
end process;
end algorithm; *)
====
