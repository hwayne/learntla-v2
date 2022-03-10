
---- MODULE duplicates_2__5 ----
EXTENDS Integers, Sequences, TLC

S == 1..10

(*--algorithm dup
variable seq \in S \X S \X S \X S;
i = 1;
seen = {};
is_unique = TRUE;

define
  TypeInvariant ==
    /\ is_unique \in BOOLEAN
    /\ seen \subseteq S
    /\ i \in 1..Len(seq)+1
    
  IsUnique(s) == 
    \A i, j \in 1..Len(s)
      i # j => seq[i] # seq[j] 

  IsCorrect == pc = "Done" => is_unique = IsUnique(seq)
end define; 

begin
  Iterate:
    while i <= Len(seq) do
      if seq[i] \notin seen then
        seen := seen \union {seq[i]};
      else
        is_unique := FALSE;
      end if;
    end while;
end algorithm; *)
====
