target: specs/reader_writer/1/reader_writer.tla
states:
  rw_1:
    states: 3
    distinct: 2
!!!
!tlacli check %
!tlacli translate %
!!!
---- MODULE reader_writer_1__1 ----
EXTENDS Integers, Sequences, TLC

(*--algorithm reader_writer
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
