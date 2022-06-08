---- MODULE reader_writer ----
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
