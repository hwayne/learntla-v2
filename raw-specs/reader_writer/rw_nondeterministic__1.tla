
---- MODULE rw_nondeterministic__1 ----
EXTENDS Integers, Sequences, TLC

Writers == {1, 2, 3}

(*--algorithm reader_writer

either write or skip;
