
---- MODULE hourclock__3 ----
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
          with x = 1 do       
            hr := hr + 1;
          end with
        end if;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-15444efefd6dbd631b1aa7593ae70afc
VARIABLE hr

vars == << hr >>

Init == (* Global variables *)
        /\ hr = 1

Next == IF hr = 12
           THEN /\ hr' = 1
           ELSE /\ LET x == 1 IN
                     hr' = hr + 1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-d61bab1363d490c3588864c3a4f39256
====
