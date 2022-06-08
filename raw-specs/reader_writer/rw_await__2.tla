target: specs/reader_writer/rw_await_2/reader_writer.tla
!!!
LoadLocal !tlacli check %
!!!
---- MODULE rw_await__2 ----
EXTENDS Integers, Sequences, TLC

Writers == {1, 2, 3}

(* --algorithm reader_writer
variables
  queue = <<>>;
  total = 0;

process writer \in Writers
begin
  AddToQueue:
    await queue = <<>>;
    queue := Append(queue, self);
end process;

process reader = 0
begin
  ReadFromQueue:
    await queue # <<>>;
      total := total + Head(queue);
      queue := Tail(queue);
    goto ReadFromQueue;
end process;
end algorithm; *)
====
