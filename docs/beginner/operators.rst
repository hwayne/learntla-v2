.. _operators:

+++++++++++++++++++++++++
Operators and Values
+++++++++++++++++++++++++

Intro
===========

Operators are what you'd think of as a function in a programming language. They take arguments and evaluate to expressions.

::

  EXTENDS Integers

  Add(x, y) == x + y


.. troubleshooting::

  If you see an error like

  > Was expecting "=====" or more Module Body, encountered ``"$Operator"`` at line $n...

  It's likely because you used a single ``=`` instead of a double ``==`` when defining the operator.


.. topic:: asdasdas

  What is a topic

Operators can take any number of arguments. There are no default values, operator overloading, or optional arguments. If an operator has two parameters, it must always take two values. If an operator takes no values, you can write it without the parens. In this case, it's effectively a programming constant.

::

  MaxVal == 17

.. note::

  Are a few special forms of operators, like higher-order operators, recursive operators, and lambdas, which we will cover `later <higher-order-operators>`.

The right-hand side of an operator is called an :dfn:`expression`.

.. _if-tla:

IF-THEN-ELSE
------------

We have three keywords for structuring expressions. These are `LET` statements, `case statements <case>`, and conditionals. We'll be introducing the first two later: LET statements are much more useful after we can write some basic operators, while case statements are fairly uncommon in TLA+ practice. That leaves conditionals:

::

  Abs(x) == IF x < 0 THEN -x ELSE x

Expressions always equal *something*, so there must always be an ``ELSE`` branch. Otherwise, this works as you'd expect it to.


Values
=========

TLA+ is an untyped formalism, due to its roots in mathematics. In practice, the model checker recognizes four primitive types and four advanced ones. We are not going to cover all of them now, just the ones that need little explanation.

.. note::
  
  If you want to get on ahead, the new types we are not talking about are `model values <model-value>`, `structs <struct>`, and `functions <function>`. Yes, operators and functions are different things.


.. _=:
.. _#:

Every value type in TLA+ has its own operators, with no overlap or overloading. The two exceptions to this are ``=`` and ``#``, which "equals" and "not equals", respectively. Values of different types cannot be tested for equality, and that will throw an error.

.. troubleshooting::

  If you see an error like

  > Encountered "Beginning of Definition" at line $n...

  It's likely because you used a double ``==`` instead of a single ``=`` when testing for equality.


.. _integer:
.. _string:

The obvious ones
----------------

Integers and strings. To get the basic addition operators, you need ``EXTENDS Integers``. Strings must use "double quotes" and cannot use single quotes. There are no operators for strings except ``=`` and ``#``. In practice, they are used as tokens. Use them as tokens. If your system needs to manipulate strings, we instead store them in a `sequence`.

.. _bool:

Booleans
--------


The booleans are ``TRUE`` and ``FALSE``.

So why do they get their own section? There's two things you need to know about booleans. First of all, the boolean operators are patterned after what mathematicians are familiar with, not what programmers are. They are:

.. list-table::
  :header-rows: 1

  * - Logic
    - TLA+ Symbol
    - Math Symbol
  * - and 
    - ``/\\``
    - :math:`wedge`
  * - or 
    - ``\/``
    - :math:`vee`
  * - not 
    - ``~``
    - :math:`neg`

A quick mnemonic: ``~`` is a little flippy thing, so it's "not". ``/\\`` looks like an "A", so it's "and". ``\/`` is the other one.

.. exercise::
  
  Write a ``Xor`` operator:

  ::
    
    Xor(TRUE, FALSE) = TRUE
    Xor(TRUE, TRUE) = FALSE


  .. solution:: TK

    ``Xor(A, B) == A = ~B``



There is one more boolean operator of note: ``=>``, or "implication". ``A => B`` means that B is true or A is false (or both). You don't see this very often in programming, as it's pretty useless for control flow. But it's *extremely* important for any kind of specification work. We'll go into much, much more detail about it later.

The other thing is that TLA+ has a "bullet point notation" for boolean logic. Let's say you need an expression like ``A /\ (B \/ C) /\ (D \/ (E /\ F))``. That's really hard to parse! So in TLA+ you, can instead write it as:

::

  /\ A
  /\ \/ B
     \/ C
  /\ \/ D
     \/ /\ E
        /\ F


That makes it much clearer. Notice that we have an extra ``/\\`` before ``A``. That's not necessary, but it makes the shape more pleasing, so we do it. **This is also the only place in the language where whitespace matters.** Lets say I instead wrote

::

  /\ A
  /\ \/ B
     \/ C
  /\ \/ D
     \/ /\ E
  /\ F

That means something different! It's now ``A /\ (B \/ C) /\ (D \/ E) /\ F``. 

.. tip:: "Why would you even want something like that?" It makes complex `invariants` *much* easier to read.


.. _sequence:

Sequences
---------

A sequence is like a list in any other language. You write it like ``<<a, b, c>>``, and the elements can be any other values (including other sequences). As with most other languages, you look up a value of the sequence with ``seq[n]``, except that instead of the range being ``0..Len(seq)-1``, it's ``1..Len(seq)``. So yeah, they're 1-indexed.

.. warning:: Did I mention they're 1-indexed? Because they're 1-indexed.

There's also a ``Sequences`` module. If you ``EXTENDS sequences``, you also get (letting ``S == <<"a">>``: 

.. list-table::
  :header-rows: 1

  * - Expression
    - Gives
  * - ``Append(S, <<"b">>)``
    - ``<<"a", "b">>``
  * - ``S \o <<"b", "c">>``
    - ``<<"a", "b", "c">>``
  * - ``Head(S)``
    - ``"a"``
  * - ``Tail(<<1, 2>>)``
    - ``<<2>>``
  * - ``Len(S)``
    - ``1``
  * - ``SubSeq(<<1, 2, 3>>, 1, 2)``
    - TODO


.. note:: There's also ``SelectSeq``, which requires a bit more machinery to understand so we'll touch on it later.


.. note:: Tuples

.. todo:: Some kind of question

.. _set:

Sets
----

A set is a collection of *unordered*, *unique* values. You write them with braces, like ``{1, 2, 3}`` or ``{<<"a">>, <<"b", "c">>}``. 

Some programming languages have sets, but they're often less important than arrays and dictionaries. In TLA+, sets are *extremely* important. There's many reasons for this. One of them is that sets define the types of values. Set of people and values. 

.. This again breaks down to whether we care about programming or specifying. 

Operators
..........

The main thing we do with sets is check if some values belong to it. We do this with ``\in``: ``x \in set`` is true iff ``x`` is an element of ``set``. ``\in`` is also used in a few other places as syntax, not just as an operator. There's also the inverse, ``\notin``.

* ``set1 \subseteq set2`` tests if every element of ``set1`` is also an element of ``set2``.

.. note:: That's "subset or equals". It's a way to sidestep the question "Is a set a subset of itself?"

We also have ways of slicing and dicing sets:

* ``set1 \union set2`` is the set of all elements in ``set1`` or ``set2`` (or both).
* ``set1 \intersect set2`` is the set of all elements in *both* sets.
* ``set1 \\ set2``, or "set difference" is the set of all elements in ``set1`` *but not* ``set2``.

.. note:: You might see ``\cup`` and ``\cap`` instead of ``\union`` and ``\intersect``. This comes from the mathematical symbols for set union and intersection, which are :math:`cup` and :math:`cap`.

.. exercise:: outer-product

Cardinality

.. tip:: 

  The easiest way to test if a set is empty is by writing ``set = {}``. Similarly, you can test if a sequence is empty by writing ``seq = <<>>``.

Sets of Values
..............

Often we want to generate sets for a given type of value. If I want to specify an hour-clock, I don't want to write
a..b

BOOLEAN

These are especially nice for `type invariants` and multiple starting states, which we will cover in the next part.

What about sets? There's a special

.. tip::

  I often see beginners try to test if "S is a subset of T" by writing ``S \in SUBSET T``. This works but adds a lot of overhead. Write ``S \subseteq T`` instead.


.. _\X:

We specify the time on a wall clock as ``<<hour, minute, second>>``, like ``<<0, 19, 12>>``. The first value can be 0-23, the second 0-59, and the third [#leapsecond]_ 0-60.  We could write this as

::

  ClockType == (0..23) \X (0..59) \X (0..60)

Try running this your `scratchfile`, and you see that 

.. exercise:: Earlier
  :label: operators-earlier


  1. Write an operator ``Earlier(t1, t2)``, which is true if ``t1`` represents an earlier time on the clock than ``t2``.


.. solution:: earlier

  ::

    Earlier(t1, t2) == 
      \/ (t1[1] < t2[1]) 
      \/ /\ t1[1] = t2[1] 
         /\ \/ t1[2] < t2[2]
            \/ /\ t1[2] = t2[2]
               /\ t1[3] < t2[3]

.. todo:: exercise parts

::

  \* Map
  Squares == {x*x: x \in 1..4}

  \* Filter
  Evens == {x \in 1..4: x % 2 = 0 }

I've found that the best way to remember which is which is by reading the colon as a "where". So the map is "x squared where x in 1..4", while the filter is "x in 1..4 where x is even".

.. exercise::

  #. Using ``ClockType`` as the set of all valid times, use a filter to get all of the times before noon (``<<12, 0, 0>>``)

  #. ???

  .. ``{t \in ClockType: t[1] < 12}``

.. _choose:

CHOOSE
........

Nothing we covered this section is "much different" from programming. Every programming language has numbers and strings and arrays, and most even have sets. They also have things like floats and hashes and fun things we don't get to play with. I'm sure you're patient enough to wait for the cool stuff, but *I'm* not, so let's introduce one neat thing we can do with sets early. If I write:

::

  CHOOSE x \in set: P(x)

It will grab us some element with the appropriate value. If there isn't such an element, it gives an error. For example, 

.. troubleshooting::

  If you see an error like

  .. todo:: error

  It's because you tried to choose over a set but couldn't find any values. Sometimes this just means you got the expression wrong. But other times, it points to an actual flaw in your system: you expected a value to exist, and it did not. Better write some error-handling logic or you'll get a nasty surprise in production.



.. note::

  What if multiple values satisfy ``CHOOSE``? In this case the only requirement is that the result is *deterministic*: the engine must always return the same value, no matter what. In practice this means that TLC will always choose the lowest value that matches the set.


.. todo:: CHOOSE

Playing with Operators
======================

asdasd

.. [#leapsecond] Fun fact, in the original ISO standard seconds could go 1-61! There were *two* leap seconds.
