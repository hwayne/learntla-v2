target: specs/duplicates/inv_4/duplicates.tla
!!!
!tlacli check % --inv TypeInvariant --inv IsCorrect
!tlacli translate %
!!!

---- MODULE duplicates_2__4 ----
EXTENDS Integers, Sequences, TLC, FiniteSets

S == 1..10

(*--algorithm dup
variable seq \in S \X S \X S \X S;
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-659afcca83c8b3f9aea7a75a58d75819
VARIABLES seq, index, seen, is_unique, pc

(* define statement *)
TypeInvariant ==
  /\ is_unique \in BOOLEAN
  /\ seen \subseteq S
  /\ index \in 1..Len(seq)+1

IsUnique(s) ==
  \A i, j \in 1..Len(s):
    i # j => seq[i] # seq[j]

IsCorrect == pc = "Done" => is_unique = IsUnique(seq)


vars == << seq, index, seen, is_unique, pc >>

Init == (* Global variables *)
        /\ seq \in S \X S \X S \X S
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-45c60ad0fcf7d1200a7543aeba3ce9ff
====
