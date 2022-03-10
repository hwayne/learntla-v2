target: specs/duplicates/2/duplicates.tla
states:
  duplicates_two_inputs:
    config: 1
    states: 14
    distinct: 12
!!!
!tlacli check %
!tlacli translate %
!!!
---- MODULE duplicates_1__2 ----
EXTENDS Integers, Sequences, TLC

(*--algorithm dup
variable seq \in {<<1, 2, 3, 2>>, <<1, 2, 3, 4>>};
index = 1;
seen = {};
is_unique = TRUE;
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b46db549b357eb4bc7b2b921a01626bd
VARIABLES seq, index, seen, is_unique, pc

vars == << seq, index, seen, is_unique, pc >>

Init == (* Global variables *)
        /\ seq \in {<<1, 2, 3, 2>>, <<1, 2, 3, 4>>}
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0f1f0bd5263fdd8396641dc6fc1031e9
====
