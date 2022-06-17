target: specs/tla/hourclock_4/hourclock.tla
states:
  hourclock_2:
    states: 24
    distinct: 12
!!!
LoadLocal !tlacli check %
!!!
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
          with x \in 0..1 do       
            hr := hr + 1;
          end with
        end if;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-224497c412c65f9e488bb9ea796850bb
VARIABLE hr

vars == << hr >>

Init == (* Global variables *)
        /\ hr = 1

Next == IF hr = 12
           THEN /\ hr' = 1
           ELSE /\ \E x \in 0..1:
                     hr' = hr + 1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2aab9a95d3f0bf1c60bf2ff0c4396578
====
