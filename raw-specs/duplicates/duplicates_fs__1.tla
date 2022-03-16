target: specs/duplicates/fs_1/duplicates.tla
states:
  duplicates_len_5_seqs:
    states: 800000
    distinct: 700000
!!!
!tlacli check % --inv TypeInvariant --inv IsCorrect
!tlacli translate %
!!!
---- MODULE duplicates_fs__1 ----
EXTENDS Integers, Sequences, TLC

(*--algorithm dup
variable seq \in [1..5 -> 1..10];
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-8db603b05e37e5586475a8ad13b71596
VARIABLES seq, index, seen, is_unique, pc

(* define statement *)
TypeInvariant ==
  /\ is_unique \in BOOLEAN
  /\ seen \subseteq 1..10
  /\ index \in 1..Len(seq)+1

IsUnique(s) ==
  \A i, j \in 1..Len(s):
    i # j => seq[i] # seq[j]

IsCorrect == pc = "Done" => is_unique = IsUnique(seq)


vars == << seq, index, seen, is_unique, pc >>

Init == (* Global variables *)
        /\ seq \in [1..5 -> 1..10]
        /\ index = 1
        /\ seen = {}
        /\ is_unique = TRUE
        /\ pc = "Iterate"

Iterate == /\ pc = "Iterate"
           /\ IF index <= Len(seq)
                 THEN /\ IF seq[index] \notin seen
                            THEN /\ seen' = (seen \union {seq[index]})
                                 /\ UNCHANGED is_unique
                            ELSE /\ is_unique' = FALSE
                                 /\ seen' = seen
                      /\ index' = index + 1
                      /\ pc' = "Iterate"
                 ELSE /\ pc' = "Done"
                      /\ UNCHANGED << index, seen, is_unique >>
           /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f9416df97d1dc4f8504f84b137ad9213
====
