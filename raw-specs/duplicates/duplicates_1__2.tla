target: specs/duplicates/2/duplicates.tla
states:
  duplicates_two_inputs:
    config: 1
    states: 14
    distinct: 12
!!!
!tlacli check %
!tlacli translate %
!!!
---- MODULE duplicates_1__2 ----
EXTENDS Integers, Sequences, TLC

(*--algorithm dup
variable seq \in {<<1, 2, 3, 2>>, <<1, 2, 3, 4>>};
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
