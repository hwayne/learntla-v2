.. _operators:

+++++++++++++++++++++++++
Operators and Values
+++++++++++++++++++++++++

We're going to model this with clock arithmetic!

Operators
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

.. _if_tla:

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

Note there is **not** a float type. Floats have incredibly complex semantics that are *extremely* hard to model-check. Usually you can abstract them out, but if you absolutely *need* floats then TLA+ is the wrong tool for the job.

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
    - ``/\``
    - :math:`\wedge`
  * - or 
    - ``\/``
    - :math:`\vee`
  * - not 
    - ``~``
    - :math:`\neg`

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
=========

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


::

  ToSeconds(time) == time[1] + time[2]*60 + time[3]*3600


.. exercise:: Earlier
  :label: operators-earlier


  1. Write an operator ``Earlier(t1, t2)``, which is true if ``t1`` represents an earlier time on the clock than ``t2``.


.. solution:: earlier

  ::

    Earlier(t1, t2) == ToSeconds(t1) < ToSeconds(t2)

.. note:: Tuples

.. todo:: Some kind of question

.. _set:

Sets
====

A set is a collection of *unordered*, *unique* values. You write them with braces, like ``{1, 2, 3}`` or ``{<<"a">>, <<"b", "c">>}``. 

Some programming languages have sets, but they're often less important than arrays and dictionaries. In TLA+, sets are *extremely* important. There's many reasons for this. One of them is that sets define the types of values. Set of people and values. 

.. This again breaks down to whether we care about programming or specifying. 

Operators
----------

The main thing we do with sets is check if some values belong to it. We do this with ``\in``: ``x \in set`` is true iff ``x`` is an element of ``set``. ``\in`` is also used in a few other places as syntax, not just as an operator. There's also the inverse, ``\notin``.

* ``set1 \subseteq set2`` tests if every element of ``set1`` is also an element of ``set2``.

.. note:: That's "subset or equals". It's a way to sidestep the question "Is a set a subset of itself?"

We also have ways of slicing and dicing sets:

* ``set1 \union set2`` is the set of all elements in ``set1`` or ``set2`` (or both).
* ``set1 \intersect set2`` is the set of all elements in *both* sets.
* ``set1 \ set2``, or "set difference" is the set of all elements in ``set1`` *but not* ``set2``.

.. note:: You might see ``\cup`` and ``\cap`` instead of ``\union`` and ``\intersect``. This comes from the mathematical symbols for set union and intersection, which are :math:`\cup` and :math:`\cap`.

.. exercise:: outer-product

Cardinality

.. tip:: 

  The easiest way to test if a set is empty is by writing ``set = {}``. Similarly, you can test if a sequence is empty by writing ``seq = <<>>``.

.. _sets_of_values:

Sets of Values
--------------

Now imagine we're writing a spec which uses clock values, and we want a quick operator to add times. I might write this as

::

  AddTimes(t1, t2) == <<t1[1] + t2[1], t1[2] + t2[2], t1[3] + t2[3]>>

Then ``AddTimes(<<2, 0, 1>>, <<1, 2, 3>>) = <<3, 2, 4>>``, and ``AddTimes(<<2, 0, 1>>, <<1, 2, 80>>) = <<3, 2, 81>>``.

And that should make the specifier in you do a double-take. Our clock can't show 81 seconds, so the answer should be ``<<3, 3, 21>>``. You can think of there being a set of valid clock values, all the way from ``<<0, 0, 0>>`` to ``<<23, 59, 59>>``, and ``AddTimes`` should always return some value in that set, almost like it has a type signature. We can enforce this in TLA+, but first we need a way of generating sets of values from values. Fortunately, for every type of value in TLA+, there's a method to generate sets of those values. [#except-strings]_

Let's start with the easiest: to get the set of all booleans, just write ``BOOLEAN``. That's the set ``{TRUE, FALSE}``. For integers, ``a..b`` is the set ``{a, a+1, a+2, ... , b}``. You need ``EXTENDS Integers`` for this to work.

.. exercise:: Sequence indices
  :label: one-len

  How do you get all of the indices of a sequence? Hint: use ``Len(seq)``.

.. solution:: one-len

  ``1..Len(seq)``

.. tip::

  If ``a > b``, then ``a..b`` is empty. This makes a lot of things a lot simpler. For example, ``1..Len(seq)`` is the set of all of ``seq``'s indices. If ``seq = <<>>``, you get ``1..0 = {}``, which is what you'd expect.


.. _\X:

Now for sequences. The :dfn:`Cartesian product` of two sets S and T is the set of all sequences where the first element is in S and the second is in T. It's written with ``\X``. For example, consider ``LoginAttempt`` containing who's logging in, the time they attempted the login, and if it was successful or not. I can represent the set of all possible such values as ``LoginAttempt == Person \X Time \X BOOLEAN`` {{explain better}}.

Speaking of ``Time``, we can combine ``\X`` and ``..`` to finally get our clock type:

::

  ClockType == (0..23) \X (0..59) \X (0..59)

As a quick sanity check, run ``Cardinality(ClockType)`` in your `scratchfile` (remember, you'll need ``EXTENDS FiniteSets``). You should see it has 86400 elements. We're now one step closer to having a property for ``AddTimes``: we want the result of it to always return a value in ``ClockType``.

.. exercise:: ???

  TODO


.. _SUBSET:

Finally, we can get all subsets of a set with ``SUBSET S``. ``SUBSET ClockType`` will be all the sets containing a bunch of clock values... all 7,464,960,000 of them. [#million]_

.. tip::

  I often see beginners try to test if "S is a subset of T" by writing ``S \in SUBSET T``. This works but is very inefficient. Write ``S \subseteq T`` instead.



What about sets? There's a special

.. todo:: exercise parts

.. todo:: should map-filter go before or after sets of elements?

::

  \* Map
  Squares == {x*x: x \in 1..4}

  \* Filter
  Evens == {x \in 1..4: x % 2 = 0 }

I've found that the best way to remember which is which is by reading the colon as a "where". So the map is "x squared where x in 1..4", while the filter is "x in 1..4 where x is even".

.. exercise:: taba
  :label: asdasd

  #. Using ``ClockType`` as the set of all valid times, use a filter to get all of the times before noon (``<<12, 0, 0>>``)

  #. ???

  .. ``{t \in ClockType: t[1] < 12}``

  .. ordered pairs



.. exercise:: Sequence Manipulations
  :label: map_filter_seq

  1. Write ``IndicesMatching(seq, val)``, which returns all indices ``i`` of ``seq`` where ``seq[i] = val``.
  2. Write ``Range(seq)``, which returns all values in ``seq``. IE ``Range(<<"a", "b", "a">>) = {"a", "b"}``.

.. solution:: map-filter-seq

  1. ``IndicesMatching(seq, val) == {i \in 1..Len(seq): seq[i] = val}``
  2. ``Range(seq) == {seq[i]: i \in 1..Len(seq)}``

.. _choose:

CHOOSE
--------

Getting the number of seconds past midnight from a clock value is straightforward. But what about going the other way? If we have a time in seconds, we can get the clock time by 

#. Floor divide by 60 to get the total minutes, and then set the remainder as "seconds".
#. Floor divide again by 60 to get the total hours.
#. Set the remainder of the second divison as minutes.

{{Talk about how this can give you ``<<25, 0, 0>>`` as a value}}

This *constructs* a clock value from the total seconds. This is how we'd do it in a programming language, where we are implementing algorithms to do things. But here's another thing we could do:

#. Take the set of all possible clock values.
#. Pick the element in the set that, when converted to seconds, gives us the value.

We don't do it this way because "the set of all possible clock values" is over 80,000 elements long and doing a find on an 80,000 element list is a waste of resources. But it more closely matches the *definition* of the conversion. Since we're not running a large app for everybody, defition > performance here. In TLA+ we can write the selection like this: 

::

  ToClock(seconds) == CHOOSE x \in ClockType: ToSeconds(x) = seconds

``CHOOSE x \in set: P(x)`` is the generic "selection" syntax. Try it in `Scratch`. 

CHOOSE is useful whenever we need to pull a value from a set.

Now what happens if we write ``ToClock(86401)``? There are no clock times that have 86,401 seconds. If you try this, TLC will raise an error. This is in contrast to the implementation solution, which will instead give us a nonsense value. 99% of the time if it can't find a corresponding element of the set, that's a bug in the specification, an edge case you didn't consider. Better to harden up the operator:
{{Notice this is more stricter than the constructive solution, which would isntead give you junk values}}
::

  ToClock(seconds) == CHOOSE x \in ClockType: ToSeconds(x) = seconds % 86400



.. troubleshooting::

  If you see an error like

  .. todo:: no element satisfied P

  It's because you a ``CHOOSE`` that couldn't find any values.  Sometimes this just means you got the expression wrong. But other times, it points to an actual flaw in your system: you expected a value to exist, and it did not. Better write some error-handling logic or you'll get a nasty surprise in production.



.. note::

  What if multiple values satisfy ``CHOOSE``? In this case the only requirement is that the result is *deterministic*: the engine must always return the same value, no matter what. In practice this means that TLC will always choose the lowest value that matches the set.


.. _let:

LET
=====

As you can imagine, TLA+ operators can get quite complex!

::

  ToClock(seconds) == 
    LET seconds_per_day == 86400 
    IN CHOOSE x \in ClockType: ToSeconds(x) = seconds % seconds_per_day

The LET gives us a new definition, locally scoped to ``ToClock``. ``seconds_per_day`` is an operator that only exists in the definition of this one.

Wait, operator? Yes, we can add parameterized operators in ``LET``, too!


.. todo:: Each operator in the LET can refer to previously defined operators in that scope. With this we can construct solutions step-by-step. 

  If you have to write a complex operator, breaking it into steps with LET is a great way to make it more understandable.
.. [#except-strings] Except strings. Well actually there is a keyword, ``STRING``, but it represents all possible strings, which is an infinitely large set, so...
.. [#leapsecond] Fun fact, in the original ISO standard seconds could go 1-61! There were *two* leap seconds.
.. [#million] If you actual try this TLC will error out, because it assumes sets with more than 1,000,000 elements are unintentional. You can raise the limit in the TLC options.
