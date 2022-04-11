
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
\* Make this use a local variable so there's no deadlock
begin
  ReadFromQueue:
    if queue # <<>> then
      total := total + Head(queue);
      queue := Tail(queue);
    end if;
end process;
end algorithm; *)
====
