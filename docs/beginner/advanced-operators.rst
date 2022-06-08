.. _chapter_advanced_operators:

++++++++++++++++
More Operators
++++++++++++++++

This isn't much more complicatedd than the last sections, but this is the best place to put it.

So we can now model concurrent algorithms and write complex liveness properties. You know what we can't do?

Add a sequence.

I mean sure, we can write a pluscal algoirhtm to do that

<alg>

But how the heck do you write ``SumSeq``?!

We *can* do this with what we've learned so far, but it's really complicated and annoying and I don't expect you to figure it out on your own. Maybe I'll push it to an advanced section. For a long time, that was the only way you could do it. But motivated by the annoyingness of it, in 2018 TLA+ was updated to include recursive operators.

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

Easy. In fac we can put the ``RECURSIVE`` part inside a `LET`, to make a helper op:

::

  SumSeq(s) == LET
    RECURSIVE Helper(_)
    Helper(s_) == IF s_ = <<>> THEN 0 ELSE
    Head(s_) + Helper(Tail(s_))
  IN Helper(s)

There's no syntactic check that the recursion ends. If you have unbound recursion then TLC will throw a stack overflow error.

.. rubric:: Summing a set and commutativity
.. todo:: Other ways to use this

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
  
.. warning:: You can't combine recursive and higher-order operators. {{Can you use a helper op?}}


.. index::
  single: Operators; Binary Operators

Binary operators
================

If you peak at the definition of the `Sequences` module, you'll see how it defines ``\o``:

::

  ...

``\o`` is a binary operator. There's a fixed set of binary operators, like ``\o``, ``+``, and ``\prec``, that you can define. On the whole I don't like doing this because it makes specs confusing, but there's a couple I use often:

::

  set ++ x == set \union {x}
  set -- x == set \ {x}


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


