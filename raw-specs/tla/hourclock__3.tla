target: specs/tla/hourclock_3/hourclock.tla
!!!
LoadLocal !tlacli check %
!!!
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
====
