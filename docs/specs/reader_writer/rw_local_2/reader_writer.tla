---- MODULE reader_writer ----
EXTENDS Integers, Sequences, TLC

(* --algorithm reader_writer
variables
  queue = <<>>;
  total = 0;

process writer = 1
variables
  i = 0;
begin
  AddToQueue:
    while i < 2 do
      queue := Append(queue, 1);
      i := i + 1;
    end while;
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
