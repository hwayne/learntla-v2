target: specs/duplicates/1/duplicates.tla
states:
  duplicates_fixed_input:
    config: 1
    states: 7
    distinct: 6
!!!
LoadLocal !tlacli check %
!!!
---- MODULE duplicates_1__1 ----
EXTENDS Integers, Sequences, TLC

(*--algorithm dup
variable seq = <<1, 2, 3, 2>>;
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
