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
====
