target: specs/duplicates/3/duplicates.tla
states:
  duplicates_many_inputs:
    config: 1
    states: 70000
    distinct: 60000
!!!
!tlacli check %
!!!
---- MODULE duplicates_1__3 ----
EXTENDS Integers, Sequences, TLC

S == 1..10

(*--algorithm dup
  variable seq \in S \X S \X S \X S;
  index = 1;
  seen = {};
  is_unique = TRUE;

begin
  Iterate:
    while index <= Len(seq) do
      if seq[index] \notin seen then
        seen := seen \union {seq[index]};
      else
        is_unique := FALSE;
      end if;
      index := index + 1;
    end while;
end algorithm; *)
====
