---- MODULE calculator ----
EXTENDS Integers, TLC
CONSTANT NumInputs

Digits == 0..9

(* --algorithm calculator
variables 
  i = 0;
  sum = 0;

begin
  Calculator:
    while i < NumInputs do
      with x \in Digits do
          \* Add
          sum := sum + x;
      end with;
      i := i + 1;
    end while;
end algorithm; *)
====
