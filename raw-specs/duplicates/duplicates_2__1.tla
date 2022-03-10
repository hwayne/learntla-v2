target: specs/duplicates/inv_1/duplicates.tla
!!!
!tlacli check % --inv TypeInvariant
!tlacli translate %
!!!
---- MODULE duplicates_2__1 ----
EXTENDS Integers, Sequences, TLC

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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-cba7cd92fb5e9071f263eb84b2b743fc
VARIABLES seq, index, seen, is_unique, pc

(* define statement *)
TypeInvariant ==
  /\ is_unique \in BOOLEAN
  /\ seen \subseteq S
  /\ index \in 1..Len(seq)+1


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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b8d9ed1bce798f95c06d08dcddad9547
====
