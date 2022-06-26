target: specs/reader_writer/rw_many_3/reader_writer.tla
states:
  rw_many_3:
    states: 69
    distinct: 38
!!!
LoadLocal !tlacli check %
!!!
---- MODULE rw_many__3 ----
EXTENDS Integers, Sequences, TLC

Writers == {1, 2, 3}

(* --algorithm reader_writer
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
====
