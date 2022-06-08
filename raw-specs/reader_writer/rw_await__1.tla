target: specs/reader_writer/rw_await_1/reader_writer.tla
states:
  rw_await:
    states: 33
    distinct: 20
!!!
LoadLocal !tlacli check %
!!!
---- MODULE rw_await__1 ----
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
    if queue # <<>> then
      total := total + Head(queue);
      queue := Tail(queue);
    end if;
    goto ReadFromQueue;
end process;
end algorithm; *)
====
