---- MODULE reader_writer ----
EXTENDS Integers, Sequences, TLC

(* --algorithm reader_writer
variables
  queue = <<>>;
  total = 0;


process writer = 1
begin
  AddToQueue:
    queue := Append(queue, 1);
end process;
end algorithm; *)
====
