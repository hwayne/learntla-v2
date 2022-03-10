---- MODULE duplicates ----
EXTENDS Integers, Sequences, TLC

S == 1..10

(*--algorithm dup
  variable seq \in S \X S \X S \X S;
i = 1;
seen = {};
all_unique = TRUE;
begin
  Iterate:
    while i <= Len(seq) do
      if seq[i] \notin seen then
        seen := seen \union {seq[i]};
      else
        all_unique := FALSE;
      end if;
    end while;
end algorithm; *)
====
