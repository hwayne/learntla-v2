---- MODULE duplicates ----
EXTENDS Integers, Sequences, TLC

(*--algorithm dup
variable n \in 1..5;
seq \in [1..n -> 1..10];
index = 1;
seen = {};
is_unique = TRUE;

define
  TypeInvariant ==
    /\ is_unique \in BOOLEAN
    /\ seen \subseteq 1..10
    /\ index \in 1..Len(seq)+1
    
  IsUnique(s) == 
    \A i, j \in 1..Len(s):
      i # j => seq[i] # seq[j] 

  IsCorrect == pc = "Done" => is_unique = IsUnique(seq)
end define; 

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
