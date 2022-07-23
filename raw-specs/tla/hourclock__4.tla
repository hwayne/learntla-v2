target: specs/tla/hourclock_4/hourclock.tla
states:
  hourclock_2:
    states: 24
    distinct: 12
!!!
LoadLocal !tlacli check %
!!!
---- MODULE hourclock__4 ----
EXTENDS Naturals
(*--fair algorithm hourclock
variable hr = 1; \* hour

begin
  A:
    while TRUE do
        if hr = 12 then
          hr := 1;
        else
          with x \in 1..2 do
            hr := hr + x;
          end with;
        end if;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d0081905" /\ chksum(tla) = "27d8122a")
VARIABLE hr

vars == << hr >>

Init == (* Global variables *)
        /\ hr = 1

Next == IF hr = 12
           THEN /\ hr' = 1
           ELSE /\ \E x \in 1..2:
                     hr' = hr + x

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 
====
