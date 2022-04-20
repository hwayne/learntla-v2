target: specs/calculator/2/calculator.tla
states:
  calculator_five_inputs_with_either:
    states: 71333
    distinct: 16551
!!!
!tlacli check % --const NumInputs 5
!!!
---- MODULE calculator__2 ----
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
