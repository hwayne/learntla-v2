target: specs/tla/hourclock_1/hourclock.tla
states:
  hourclock_1:
    states: 13
    distinct: 12
    
!!!
LoadLocal !tlacli check %
!!!
---- MODULE hourclock__1 ----
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
====
