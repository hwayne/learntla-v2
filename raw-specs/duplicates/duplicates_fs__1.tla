target: specs/duplicates/fs_1/duplicates.tla
states:
  duplicates_len_5_seqs:
    states: 800000
    distinct: 700000
!!!
!tlacli check % --inv TypeInvariant --inv IsCorrect --const S "{1, 2, 3, 4, 5, 6, 7, 8, 9, 10}"
!tlacli translate %
!!!
---- MODULE duplicates_fs__1 ----
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT S
ASSUME Cardinality(S) >= 4

(*--algorithm dup
variable
  seq \in [1..5 -> S];
  index = 1;
  seen = {};
  is_unique = TRUE;

define
  TypeInvariant ==
    /\ is_unique \in BOOLEAN
    /\ seen \subseteq S
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
