.. _chapter_advanced_operators:

++++++++++++++++
More Operators
++++++++++++++++

This isn't much more complicated than the last sections, but this is the best place to put it. So we can now model concurrent algorithms and write complex liveness properties. You know what we can't do?

Sum up a sequence.

I mean sure, we can write a Pluscal algorithm to do that:

.. spec:: advanced_operators/sum.tla

But how the heck do you write ``SumSeq``?!

We *can* do this with what we've learned so far, but it's really complicated and annoying and I don't expect you to figure it out on your own. Maybe I'll push it to a topic or something. But motivated by the annoyingness of summing sequences, in 2008 TLA+ was updated to include recursive operators.

.. index:: 
  single: RECURSIVE
  single: Operators; Recursive Operators
  

.. _recursive:

Recursive Operators
===================

Recursive operators have to be predefined, like this:

::

  RECURSIVE SumSeq(_)

The ``(_)`` is the number of arguments you want in advance. So for a 2-parameter operator, you'd write ``Op(_, _)``. Once you've done this, you can define the operator as normal, except it's able to reference itself:


::

  SumSeq(s) == IF s = <<>> THEN 0 ELSE
    Head(s) + SumSeq(Tail(s))

Easy. In fact we can put the ``RECURSIVE`` part inside a `LET`, to make a helper op:

::

  SumSeq(s) == LET
    RECURSIVE Helper(_)
    Helper(s_) == IF s_ = <<>> THEN 0 ELSE
    Head(s_) + Helper(Tail(s_))
  IN Helper(s)

There's no syntactic check that the recursion ends. If you have unbound recursion then TLC will throw a stack overflow error.

.. rubric:: Recursion on a set and commutativity

If we want to do the same thing with summing a set, we need a way to pick a single element for recursion. Naturally, the easiest way to do that is with `CHOOSE`.

::

  RECURSIVE SetSum(_)

  SetSum(set) == IF set = {} THEN 0 ELSE 
    LET x == CHOOSE x \in set: TRUE
      IN x + SetSum(set \ {x})

Seeing this should worry you. There isn't a unique choice of ``x``: *every* element of the set satisfies ``TRUE``! This means that `TLC will choose the lowest value <choose_deterministic>`. 

::

  RECURSIVE SetToSeq(_)

  SetToSeq(set) == IF set = {} THEN <<>> ELSE 
    LET x == CHOOSE x \in set: TRUE
      IN <<x>> \o SetToSeq(set \ {x})
              
.. code:: none

  >>> SetToSeq({6, 8, 1, 2, -1, 5})

  <<-1, 1, 2, 5, 6, 8>>

Sometimes this doesn't matter like in ``SetSum``. But if it might, you should specify a unique selection predicate for your choose, like explicitly choosing the minimum value.


.. index::
  single: Operators; Higher-order operators
  single: LAMBDA

Higher-order Operators
======================

Next up: operators that take other operators as functions. That way we can have ``SeqMap``. Here's how we can define ``SeqMap`` with a function:

::

  SeqMap(f, seq) == [i \in DOMAIN seq |-> f[seq[i]]]

But if we want to use an operator, we'd write it this way instead:

::

  SeqMap(Op(_), seq) == [i \in DOMAIN seq |-> Op([seq[i]])]

Not too bad. You can define anonymous operators with ``LAMBDA``:

::

  SeqMap(LAMBDA x: x + 1, <<1, 2, 3>>)
  \* <<2, 3, 4>>
  
.. warning:: You can't combine recursive and higher-order operators.

.. index::
  single: Operators; Binary Operators

Binary operators
================

If you `peek <toolbox_misc>` at the definition of the ``Sequences`` module, you'll see how it defines ``\o``:

::

  s \o t == [i \in 1..(Len(s) + Len(t)) |-> IF i \leq Len(s) THEN s[i]
                                                           ELSE t[i-Len(s)]]

``\o`` is a binary operator. There's a fixed set of binary operators, like ``\o``, ``+``, and ``\prec``, that you can define. On the whole I don't like doing this because it makes specs confusing, but there's a couple I use often:

::

  set ++ x == set \union {x}
  set -- x == set \ {x}

Function Operators
==================

This is a bit of syntactic sugar for writing top-level functions:

.. code-block:: tla

  Double == [x \in 1..10 |-> x * 2]
  
  \* can also be written as

  Double[x \in 1..10] == x * 2

This is primarily for writing recursive functions::

  Factorial[x \in 0..10] == IF x = 0 THEN 1 ELSE x * Factorial[x - 1]

  
.. index:: CASE
.. _CASE:

CASE
=========

I had nowhere else to put this so I'm just dumping it here for completion's sake.

::
  
  Fizzbuzz(x) ==
    CASE (x % 3 = 0) /\ (x % 5 = 0) -> "Fizzbuzz"
      [] (x % 3 = 0)                -> "Fizz"
      [] (x % 5 = 0)                -> "Buzz"
      [] OTHER                      -> x

If nothing matches (and you didn't have an ``OTHER``), then TLC raises an error. If more than one thing matches, it's implementation-defined what actually is executed, and TLC will pick the first choice that matches.


