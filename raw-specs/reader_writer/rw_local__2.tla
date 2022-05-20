target: specs/reader_writer/rw_local_2/reader_writer.tla
states:
  rw_local_2:
    states: 15
    distinct: 11
!!!
!tlacli check %
!!!
---- MODULE rw_local__2 ----
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
