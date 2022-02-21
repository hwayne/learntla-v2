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


Operators can take any number of arguments. There are no default values, operator overloading, or optional arguments. If an operator has two parameters, it must always take two values. If an operator takes no values, you can write it without the parens. In this case, it's effectively a programming constant.

::

  MaxVal == 17

.. note::

  Are a few special forms of operators, like higher-order operators, recursive operators, and lambdas, which we wil cover `later <higher-order-operators>`.

The right-hand side of an operator is called an :dfn:`expression`.

.. _if-tla:

IF-THEN-ELSE
------------

We have three keywords for structuring expressions. These are `LET` statements, `case statements <case>`, and conditionals. We'll be introducing the first two later: LET statements are much more useful after we can write some basic operators, while case statements are fairly uncommon in TLA+ practice. That leaves conditionals:

::

  Abs(x) == IF x < 0 THEN -x ELSE x

Expressions always equal *something*, so there must always be an ``ELSE`` branch. Otherwise, this works as you'd expect it to.


Whitespace
..........

Operators have a fairly small amount of 


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

..
  and :math:`wedge` /\
  or :math:`vee` \/
  not :math:`neg` ~

A quick mnemonic: ``~`` is a little flippy thing, so it's "not". ``/\\`` looks like an "A", so it's "and". ``\/`` is the other one.

.. exercise::
  
  Write a ``Xor`` operator:

  ::
    
    Xor(TRUE, FALSE) = TRUE
    Xor(TRUE, TRUE) = FALSE


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

.. _set:

Sets
----

A set is a collection of *unordered*, *unique* values.

Operators
..........

``\in``
``\subseteq``
``\union``
``\intersect``
``\\``

.. note:: You might see 

.. note:: That's "subset or equals". It's a way to sidestep the question "Is a set a subset of itself?"

.. todo:: ``\notin``

Cardinality

.. technique:: The easiest way to test if a set is empty is by writing ``set = {}``.

Sets of Values
..............

a..b

BOOLEAN

These are especially nice for `type invariants` and multiple starting states, which we will cover in the next part.

What about sets? There's a special 

.. tip::

  I often see beginners try to test if "S is a subset of T" by writing ``S \in SUBSET T``. This works but adds a lot of overhead. Write ``S \subseteq T`` instead.


::

  \* Map
  Squares == {x*x: x \in 1..4}

  \* Filter
  Evens == {x \in 1..4: x % 2 = 0 }

I've found that the best way to remember which is which is by reading the colon as a "where". So the map is "x squared where x in 1..4", while the filter is "x in 1..4 where x is even".


.. todo:: non-enumerable sets

.. _sequence:

Sequences
---------
