target: specs/calculator/1/calculator.tla
states:
  calculator_five_inputs_no_either:
    states: 1043
    distinct: 187
!!!
!tlacli check % --const NumInputs 5
!!!
---- MODULE calculator__1 ----
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
