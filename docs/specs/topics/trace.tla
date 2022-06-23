---- MODULE trace ----

EXTENDS Integers, TLC

(*--algorithm errortrace
variable x=0; y=0; i=0;

define
  xyleq10 == x * y <= 10
end define;

process incX = "incX"
begin
  EtX:
    while i < 8 do
      x := x + 1;
      i := i + 1;
    end while;
end process;

process incY = "incY"
begin
  EtY:
    while i < 8 do
      y := y + 1;
      i := i + 1;
    end while;
end process;

end algorithm; *)


====

