!!!
!tlacli check %
!!!
---- MODULE hourclock__1 ----
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
            hr := hr + 1;
        end if;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ae613581e622a914b02a979e72c6acdc
VARIABLE hr

vars == << hr >>

Init == (* Global variables *)
        /\ hr = 1

Next == IF hr = 12
           THEN /\ hr' = 1
           ELSE /\ hr' = hr + 1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a9c7ba5bb67680feb3a8f76d62b0dec6
====
