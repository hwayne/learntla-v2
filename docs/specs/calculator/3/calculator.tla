---- MODULE calculator ----
EXTENDS Integers, TLC
CONSTANT NumInputs, Target

Digits == 0..9

(* --algorithm calculator
variables 
  i = 0;
  sum = 0;
define
  Invariant == sum # Target
end define;

begin
  Calculator:
    while i < NumInputs do
      with x \in Digits do
        either
          \* Add
          sum := sum + x;
        or
          \* Subtract
          sum := sum - x;
        or
          \* Multiply
          sum := sum * x;
        end either;
      end with;
      i := i + 1;
    end while;
end algorithm; *)
====
