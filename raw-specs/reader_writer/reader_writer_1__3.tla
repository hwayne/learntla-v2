target: specs/reader_writer/3/reader_writer.tla
states:
  rw_2:
    states: 7
    distinct: 5
!!!
!tlacli check %
!tlacli translate %
!!!
---- MODULE reader_writer_1__3 ----
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
