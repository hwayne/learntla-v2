
---- MODULE hourclock__4 ----
\* TODO: two clocks
EXTENDS Naturals
(*--algorithm hourclock
variable hr = 1; \* hour

begin
  A:
    while TRUE do
        if hr = 12 then
          hr := 1;
        else
          with x \in 1..2 do       
            hr := hr + 1;
          end with
        end if;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-fe16fad6be60480d044877bc4d82e0e1
VARIABLE hr

vars == << hr >>

Init == (* Global variables *)
        /\ hr = 1

Next == IF hr = 12
           THEN /\ hr' = 1
           ELSE /\ \E x \in 1..2:
                     hr' = hr + 1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-9b149e815132258018f9be6e24a6d9b5
====
