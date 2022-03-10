target: specs/duplicates/2/duplicates.tla
states:
  duplicates_two_inputs:
    config: 1
    states: 8
    distinct: 6
!!!
!tlacli check %
!tlacli translate %
!!!
---- MODULE duplicates_1__2 ----
EXTENDS Integers, Sequences, TLC

(*--algorithm dup
  variable seq \in {<<1, 2, 3, 2>>, <<1, 2, 3, 4>>};
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-93b7d0c4e5a3696164c4a53cf9836ba6
VARIABLES seq, i, seen, all_unique, pc

vars == << seq, i, seen, all_unique, pc >>

Init == (* Global variables *)
        /\ seq \in {<<1, 2, 3, 2>>, <<1, 2, 3, 4>>}
        /\ i = 1
        /\ seen = {}
        /\ all_unique = TRUE
        /\ pc = "Iterate"

Iterate == /\ pc = "Iterate"
           /\ IF i <= Len(seq)
                 THEN /\ IF seq[i] \notin seen
                            THEN /\ seen' = (seen \union {seq[i]})
                                 /\ UNCHANGED all_unique
                            ELSE /\ all_unique' = FALSE
                                 /\ seen' = seen
                      /\ pc' = "Iterate"
                 ELSE /\ pc' = "Done"
                      /\ UNCHANGED << seen, all_unique >>
           /\ UNCHANGED << seq, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-56d2be8f9497b78290e8344881fbfc67
====
