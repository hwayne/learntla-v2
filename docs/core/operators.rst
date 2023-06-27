.. _operators:

+++++++++++++++++++++++++
Operators and Values
+++++++++++++++++++++++++


.. index::
  single: operator
  single: ==

Operators
===========

Operators are what you'd think of as a function in a programming language. They take arguments and evaluate to expressions.

::

  EXTENDS Integers

  MinutesToSeconds(m) == m * 60


.. troubleshooting::

  If you see an error like

    Was expecting "=====" or more Module Body, encountered ``"$Operator"`` at line $n...

  It's likely because you used a single ``=`` instead of a double ``==`` when defining the operator.

Operators can take any number of arguments. There are no default values, overloaded definitions, or optional arguments. If an operator has two parameters, it must always take two values. If an operator takes no values, you can write it without the parens. In this case, it's effectively a constant.

::

  SecondsPerMinute == 60

.. note::

  There are a few special forms of operators, like higher-order operators, recursive operators, and lambdas, which we will cover `later <chapter_advanced_operators>`.

The right-hand side of an operator is called an :dfn:`expression`.

.. index:: IF
.. _if_tla:

IF-THEN-ELSE
------------

We have three keywords for structuring expressions. These are `let` statements, `case statements <case>`, and conditionals. We'll be introducing the first two later: LET statements are much more useful after we can write some basic operators, while case statements aren't used very often. That leaves conditionals:

::

  Abs(x) == IF x < 0 THEN -x ELSE x

Expressions always equal *something*, so there must always be an ``ELSE`` branch. Otherwise, this works as you'd expect it to.

Values
=========

TLA+ is an "untyped" language, due to its roots in mathematics. In practice, the model checker recognizes four primitive types and four complex ones.

- **Primitive**: `strings <string>`, `booleans <boolean>`, `integers <integer>`, and `model values <model_values>`.
- **Complex**: `sets <set>`, `sequences <sequence>`, `structures <struct>`, and `functions <function>`.


.. index:: =, # (not equals)

Every value type in TLA+ has its own operators, with no overlap or overloading. The two exceptions to this are ``=`` and ``#``, which "equals" and "not equals", respectively. Values of different types cannot be tested for equality, and that will throw an error.

.. troubleshooting::

  If you see an error like

    Encountered "Beginning of Definition" at line $n...

  It's likely because you used a double ``==`` instead of a single ``=`` when testing for equality.

We'll leave the more sophisticated types for later and focus now on just strings, booleans, integers, and sets.

.. _string:
.. _integer:

The obvious ones
----------------

Integers and strings. To get the basic addition operators, you need ``EXTENDS Integers``. Strings must use "double quotes" and cannot use single quotes. There are no operators for strings except ``=`` and ``#``. In practice, they are used as opaque identifiers, similar to how some languages have a `:symbol type <https://ruby-doc.org/core-2.5.0/Symbol.html>`__. If your system needs to manipulate strings, we instead store them in a `sequence <sequence>`.

Note there is **not** a float type. Floats have complex semantics that are *extremely* hard to represent. Usually you can abstract them out, but if you absolutely *need* floats then TLA+ is the wrong tool for the job.

.. index::
  /\ (and), \/ (or), ~ (not)

.. _boolean:

Booleans
--------

The booleans are ``TRUE`` and ``FALSE``.

So why do they get their own section? First of all, the boolean operators look like mathematical symbols, not programming symbols. They are:

.. list-table::
  :header-rows: 1

  * - Logic
    - TLA+ Symbol
    - Math Symbol
  * - and
    - ``/\``
    - :math:`\wedge`
  * - or
    - ``\/``
    - :math:`\vee`
  * - not
    - ``~``
    - :math:`\neg`

A quick mnemonic: ``~`` is a little flippy thing, so it's "not". ``/\`` looks like an "A", so it's "and". ``\/`` is the other one. We can use these to build the other operators, like ``Xor``::

  Xor(A, B) == A = ~B

.. index:: => (implies)
.. _=>:

There is one more boolean operator of note: ``=>``, or "implication". ``A => B`` means "A is at least as true as B". ``A => B = FALSE`` when false if A is true and B is false, otherwise it's true. B is true or A is false (or both). You don't see this very often in programming, as it's pretty useless for control flow. But it's *extremely* important for any kind of specification work. We'll go into more detail about it `later <using_=>>`. [#iff]_

.. exercise:: Contrapositives
  :name: contrapositive

  1. Rewrite ``A => B`` using the "regular three" programming operators.

    .. solution::

      ::

        ~A \/ B

  2. For what values of ``A`` and ``B`` is ``~B => ~A`` true?

    .. solution::

      Using the same rewrite rule as part 1, we get ``~~B \/ ~A``, aka ``~A \/ B``, which means it has the same truth values as ``A => B``. ``~B => ~A`` is called the **contrapositive** of ``A => B``.


The other thing is that TLA+ has a "bullet point notation" for boolean logic. Let's say you need an expression like ``A /\ (B \/ C) /\ (D \/ (E /\ F))``. That's really hard to read! So in TLA+ you can instead write it as:

::

  /\ A
  /\ \/ B
     \/ C
  /\ \/ D
     \/ /\ E
        /\ F


That makes it much clearer. Notice that we have an extra ``/\`` before ``A``. That's not necessary, but it makes the shape more pleasing, so we do it. **This is also the only place in the language where whitespace matters.** Lets say I instead wrote

::

  /\ A
  /\ \/ B
     \/ C
  /\ \/ D
     \/ /\ E
  /\ F

That means something different! It's now ``A /\ (B \/ C) /\ (D \/ E) /\ F``.

.. tip:: "Why would you even want something like that?" It makes complex :doc:`invariants <invariants>` *much* easier to read.


.. index::
  single: sequence
  single: types; sequence
  :name: sequence

Sequences
=========

A sequence is like a list in any other language. You write it like ``<<a, b, c>>``, and the elements can be any other values (including other sequences). As with most other languages, you look up a value of the sequence with ``seq[n]``, except that instead of the indices being ``0..Len(seq)-1``, it's ``1..Len(seq)``. So yeah, they're 1-indexed.

.. warning:: Did I mention they're 1-indexed? Because they're 1-indexed.

There's also a ``Sequences`` module. If you ``EXTENDS Sequences``, you also get (letting ``S == <<"a">>``):

.. todo:: {PLAN} how to integrate modules and operations in modules

.. index:: Append, Head, Tail, Len, SubSeq
.. index:: \o (concat)

.. list-table::
  :header-rows: 1

  * - Expression
    - Gives
  * - ``Append(S, "b")``
    - ``<<"a", "b">>``
  * - ``S \o <<"b", "c">>``
    - ``<<"a", "b", "c">>``
  * - ``Head(S)``
    - ``"a"``
  * - ``Tail(<<1, 2, 3>>)``
    - ``<<2, 3>>``
  * - ``Len(S)``
    - ``1``
  * - ``SubSeq(<<1, 3, 5>>, 1, 2)``
    - ``<<1, 3>>``

.. troubleshooting::

  If you see an error like

    Encountered "EXTENDS" at line 3, column 1 and token "Sequences"

  It's because you wrote two separate ``EXTENDS`` lines. TLA+ can only have one ``EXTENDS`` *line* per spec, but you can have multiple modules (separated by commas) on it. So instead write ``EXTENDS Integers, Sequences`` and you should be fine.

With sequences, we can represent a 24-hour clock as ``<<hour, minute, second>>``.

::

  EXTENDS Integers, Sequences

  ToSeconds(time) == time[1]*3600 + time[2]*60 + time[3]
  Earlier(t1, t2) == ToSeconds(t1) < ToSeconds(t2)


.. note:: Fixed-length sequences are also called "tuples". It's the same syntax either way.

.. index:: set
  :name: set

Sets
====

A set is a collection of *unordered*, *unique* values. You write them with braces, like ``{1, 2, 3}`` or ``{<<"a">>, <<"b", "c">>}``. You can even have sets inside other sets, like ``{{1}, {2}, {3}}``.

Sets cannot contain elements of different types; ``{1, "a"}`` is invalid.


.. index:: set; set operators, \in; x \in set
.. index:: \notin
.. index:: \subseteq
.. _set_operators:

Set Operators
--------------

To check if ``x`` is an element of ``set``, we write ``x \in set``. ``\in`` is used in a few other places as syntax, not just as an operator. There's also the inverse, ``\notin``. ``set1 \subseteq set2`` tests if every element of ``set1`` is also an element of ``set2``.

.. note:: That's "subset or equals". It's a way to sidestep the question "Is a set a subset of itself?"

.. index:: \ (set difference), \union, \intersect

We also have ways of slicing and dicing sets:

* ``set1 \union set2`` is the set of all elements in ``set1`` or ``set2`` (or both).
* ``set1 \intersect set2`` is the set of all elements in *both* sets.
* ``set1 \ set2``, or "set difference" is the set of all elements in ``set1`` *but not* ``set2``.

.. note:: You might see ``\cup`` and ``\cap`` instead of ``\union`` and ``\intersect``. This comes from the mathematical symbols for set union and intersection, which are :math:`\cup` and :math:`\cap`.

.. code:: none

  >>> {1, 3} \union {1, 5}

  {1, 3, 5}

  >>> {1, 3} \intersect {1, 5}

  {1}

  >>> {1, 3} \ {1, 5}

  {3}

.. _Cardinality:

If you ``EXTEND FiniteSets``, you also get ``Cardinality(set)``, which is the number of elements in the set.

.. tip::

  The easiest way to test if a set is empty is by writing ``set = {}``. Similarly, you can test if a sequence is empty by writing ``seq = <<>>``.

.. _sets_of_values:

Sets of Values
--------------

Now imagine we're writing a spec which uses clock values, and we want a quick operator to add times. I might write this as

::

  AddTimes(t1, t2) == <<t1[1] + t2[1], t1[2] + t2[2], t1[3] + t2[3]>>

Then ``AddTimes(<<2, 0, 1>>, <<1, 2, 3>>) = <<3, 2, 4>>``, and ``AddTimes(<<2, 0, 1>>, <<1, 2, 80>>) = <<3, 2, 81>>``.

Wait, 81 seconds? Our clock can't show 81 seconds, the answer should be ``<<3, 3, 21>>``. You can think of there being a set of valid clock values, all the way from ``<<0, 0, 0>>`` to ``<<23, 59, 59>>``, and ``AddTimes`` should always return some value in that set, almost like it has a type signature. We can enforce this in TLA+, but first we need a way of generating sets of values from values. Fortunately, for every type of value in TLA+, there's a method to generate sets of those values. [#except-strings]_

.. index::
  single: BOOLEAN
  single: .. (set interval)
  single: sets of; booleans
  single: sets of; numbers

Let's start with the easiest: to get the set of all booleans, just write ``BOOLEAN``. That's the set ``{TRUE, FALSE}``. For integers, ``a..b`` is the set ``{a, a+1, a+2, ... , b}``. You need ``EXTENDS Integers`` for this to work.

.. tip::

  If ``a > b``, then ``a..b`` is empty. This makes a lot of things a lot simpler. For example, ``1..Len(seq)`` is the set of the indices of ``seq``. If ``seq = <<>>``, you get ``1..0 = {}``, which is what you'd expect.

.. index::
  single: \X
  single: sequence; sequence sets
  single: sets of; sequences

.. _\X:

Now for sequences. The :dfn:`Cartesian product` of two sets S and T is the set of all sequences where the first element is in S and the second is in T. It's written with ``\X``. For example, consider ``LoginAttempt`` containing who's logging in, the time they attempted the login, and if it was successful or not. I can represent the set of all possible such values as ``LoginAttempt == Person \X Time \X BOOLEAN``.

.. note::

  ``\X`` is *not* associative:

    .. code:: none

      S == 1..3

      >> <<1, 2, 3>> \in S \X S \X S
      TRUE

      >> <<1, 2, 3>> \in (S \X S) \X S
      FALSE

      >> <<<<1, 2>>, 3>> \in (S \X S) \X S
      TRUE

Speaking of ``Time``, we can combine ``\X`` and ``..`` to finally get our clock type:

::

  ClockType == (0..23) \X (0..59) \X (0..59)

As a quick sanity check, run ``Cardinality(ClockType)`` in your `scratch` (remember, you'll need ``EXTENDS FiniteSets``). You should see it has 86400 elements. We're now one step closer to having a property for ``AddTimes``: we want the result of it to always return a value in ``ClockType``.


.. index:: SUBSET, set; set sets, sets of; sets
.. _SUBSET:

Finally, we can get all subsets of a set with ``SUBSET S``. ``SUBSET ClockType`` will be all the sets containing a bunch of clock values... all 2^86400 of them. *Don't do this.*

.. tip::

  I often see beginners try to test if "S is a subset of T" by writing ``S \in SUBSET T``. This works but is very inefficient. Write ``S \subseteq T`` instead.


.. _map:
.. _filter:

Map and Filter
..............

Sets can be mapped and filtered.

::

  \* Map
  Squares == {x*x: x \in 1..4}

  \* Filter
  Evens == {x \in 1..4: x % 2 = 0 }

I've found that the best way to remember which is which is by reading the colon as a "where". So the map is "x squared where x in 1..4", while the filter is "x in 1..4 where x is even".

To get all the times in the second half of each hour, we could write:

::

  {t \in ClockType: t[2] >= 30 /\ t[3] = 0}


Map and filter are great for utility, too. The *range* of a sequence is the set of all elements in the sequence. We can get that with a set map:

::

  Range(seq) == {seq[i]: i \in 1..Len(seq)}


.. index:: CHOOSE, \in; x \in set

.. _CHOOSE:

CHOOSE
--------

Getting the number of seconds past midnight from a clock value is straightforward. But what about going the other way? If we have a time in seconds, we can get the clock time by

#. Floor divide by 3600 to get the total hours.
#. Floor divide again the remainder by 60 to get the total minutes.
#. Take the remainder of the second division as seconds.

This *constructs* a clock value from the total seconds. This is how we'd do it in a programming language, where we are implementing algorithms to do things. But it's also error-prone. What happens if I pass in 90,000? Then this would give me ``<<25, 0, 0>>`` — a value outside of our ``ClockType``.

Here's another thing we could do:

#. Take the set of all possible clock values.
#. Pick the element in the set that, when converted to seconds, gives us the value.

We don't do it this way because "the set of all possible clock values" is over 80,000 elements long and doing a find on an 80,000 element list is a waste of resources. But it more closely matches the *definition* of the conversion, making it more useful for *specification*. In TLA+ we can write the selection like this:

::

  ToClock(seconds) == CHOOSE x \in ClockType: ToSeconds(x) = seconds

``CHOOSE x \in set: P(x)`` is the generic "selection" syntax. Try it in `scratch`.

CHOOSE is useful whenever we need to pull a value from a set.

Now what happens if we write ``ToClock(86401)``? There are no clock times that have 86,401 seconds. If you try this, TLC will raise an error. This is in contrast to the implementation solution, which will instead give us a nonsense value. 99% of the time if it can't find a corresponding element of the set, that's a bug in the specification, an edge case you didn't consider. Better to harden up the operator:

::

  ToClock(seconds) == CHOOSE x \in ClockType: ToSeconds(x) = seconds % 86400



.. troubleshooting::

  If you see an error like

    | Attempted to compute the value of an expression of form
    | CHOOSE x \in S: P, but no element of S satisfied P.

  It's because you wrote a ``CHOOSE`` that couldn't find any values.  Sometimes this just means you got the expression wrong. But other times, it points to an actual flaw in your system: you expected a value to exist, and it did not. Better write some error-handling logic or you'll get a nasty surprise in production.


.. _choose_deterministic:

.. warning::

  What if multiple values satisfy ``CHOOSE``? In this case the only requirement is that the result is *deterministic*: the engine must always return the same value, no matter what. In practice this means that TLC will always choose the lowest value that matches the set.



.. index:: LET
.. _LET:

LET
=====

As you can imagine, TLA+ operators can get quite complex! To make them easier to follow, we can break them into suboperators, using ``LET``:

::

  ToClock(seconds) ==
    LET seconds_per_day == 86400
    IN CHOOSE x \in ClockType: ToSeconds(x) = seconds % seconds_per_day

The LET gives us a new definition, locally scoped to ``ToClock``. ``seconds_per_day`` is an operator that only exists in the definition of this one.

Wait, operator? Yes, we can add parameterized operators in ``LET``, too!

::

   ThreeMax(a, b, c) ==
      LET
        Max(x, y) == IF x > y THEN x ELSE y
      IN
        Max(Max(a, b), c)

And you can define multiple operators in the same LET:

::

   ThreeMax(a, b, c) ==
      LET
        Max(x, y) == IF x > y THEN x ELSE y
        maxab == Max(a, b)
      IN
        Max(maxab, c)

Each operator in the LET can refer to previously defined operators in that scope. With this we can construct solutions step-by-step.

Let's calculate ``ToClock`` the "programming way":

  ::

    ToClock2(seconds) ==
      LET
        h == seconds \div 3600
        h_left == seconds % 3600
        m == h_left \div 60
        m_left == h_left % 60
        s == m_left
      IN
        <<h, m, s>>

.. code:: none

  >>> ToClock2(90000)

  <<25, 0, 0>>

If you have to write a complex operator, breaking it into steps with LET is a great way to make it more understandable.

Summary
========

- Operators are top-level "functions", and evaluate to expressions. They are written ``Op(a, b) == expr``, with two equal-signs.

  - Operators can have conditions with ``IF-THEN-ELSE``, and suboperators with ``LET-IN``.

- Sequences are collections of ordered values, and are 1-indexed.
- Logic is ``/\`` for "and", ``\/`` for "or", and ``~`` for "not".

  - Logical statements can be written "bullet-points" style.

- Sets are collections of unordered, unique values.

  - We can test if an element is ``\in`` a set or if a set is a ``\subseteq`` of another set.
  - We can ``\union``, ``\intersect``, and \ (set difference) two sets.
  - We can CHOOSE elements of sets.

- All types have "sets of" that type. For integers it's ``a..b``, for booleans it's ``BOOLEAN``, for sets it's ``SUBSET``, and for sequences it's ``S1 \X S2``.

  - We can map and filter sets.


.. [#except-strings] Except strings. Well actually there is a keyword, ``STRING``, but it represents all possible strings, which is an infinitely large set, so...
.. [#iff] There's also ``A <=> B`` for "A and B are both true or both false", but it's the same thing as writing ``A = B``.
