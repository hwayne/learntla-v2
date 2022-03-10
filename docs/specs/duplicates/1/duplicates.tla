---- MODULE duplicates ----
EXTENDS Integers, Sequences, TLC

(*--algorithm dup
variable seq = <<1, 2, 3, 2>>;
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
