------------------------------ MODULE duplicates_basic ------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

IsUnique(s) == 
  \A i, j \in 1..Len(s):
    i # j => s[i] # s[j]

S == 1..10
(*--algorithm duplicates
\*variable seq = <<1, 2, 3, 2>>;
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
    
  Check:
    if all_unique then
      assert Len(seq) = Cardinality(seen);
    else
      assert Len(seq) > Cardinality(seen);
    end if;
end algorithm;*)
====
