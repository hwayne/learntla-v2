target: specs/duplicates/fs_2/duplicates.tla
states:
  duplicates_len_5_or_less:
    states: 876540
    distinct: 765430
!!!
!tlacli check % --inv TypeInvariant --inv IsCorrect
!tlacli translate %
!!!

---- MODULE duplicates_fs__2 ----
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-cff59d7548e2443e59923b0cce6b2d80
VARIABLES n, seq, index, seen, is_unique, pc

(* define statement *)
TypeInvariant ==
  /\ is_unique \in BOOLEAN
  /\ seen \subseteq 1..10
  /\ index \in 1..Len(seq)+1

IsUnique(s) ==
  \A i, j \in 1..Len(s):
    i # j => seq[i] # seq[j]

IsCorrect == pc = "Done" => is_unique = IsUnique(seq)


vars == << n, seq, index, seen, is_unique, pc >>

Init == (* Global variables *)
        /\ n \in 1..5
        /\ seq \in [1..n -> 1..10]
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
           /\ UNCHANGED << n, seq >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-86c94fbc3896203da8378af0f256c2d6
====
