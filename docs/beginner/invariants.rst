.. _chapter_invariants:

++++++++++++++++++++++++
Writing an Invariant
++++++++++++++++++++++++

.. index:: Invariant
.. _invariant:

Invariants
=============

In the last chapter, we wrote a simple specification for finding duplicates in a sequence. How do we know it's working, though? Here's another spec for finding duplicates that also runs without error:

::

  (*--algorithm find_duplicates
  variables
    seq \in S \X S \X S \X S;
    all_unique = TRUE;
  begin
    all_unique := FALSE;
  end algorithm; *)


This just says that every single sequence has duplicates! So, like in programming, we want to write some kind of automated test to verify this is correct.

In TLA+, the basic test we have is the :dfn:`invariant`. An invariant is something that must be true on every single step of the program, regardless of the initial values, regardless of where we are. 

The most common invariant we use in programming: static types! When I have a variable of type ``boolean``, I'm saying that all points in the program, the value of that variable is always true or false, never a string or 17. We can write that as a TLA+ operator:

::

  TypeInvariant ==
    /\ all_unique \in BOOLEAN


.. index:: define
  :name: define

This operator needs to know about the ``all_unique`` variable, so we have to put it after the definition in PlusCal. There's a special block, the ``define`` block, we can put between variable definition and the algorithm proper. A define block contains pure TLA+ operators, and the operators may reference the values of PlusCal variables.

.. spec:: duplicates/inv_1/duplicates.tla
  :diff: duplicates/3/duplicates.tla
  :ss: duplicates_many_inputs

To check this, we add it as an :doc:`invariant <setup>`. TLC will check it at every possible state. All of the invariants passing looks the same as us not having any invariants— TLC will only do something interesting if the invariant fails. Here's what happens if we instead change the invariant to ``all_unique = TRUE``:

.. todo:: {SCREENSHOT}

.. todo:: {CONTENT} talk about the error trace

  There's a little more we can do with the error trace, see here.


So back to the nature of the invariant. We say ``all_unique`` is the boolean type by writing that it's an element of the set of all booleans. "Types" in TLA+s are just arbitrary sets of values. We could say that ``i`` is an integer, but we can be even more exact than that. We know that the it represents an index of ``seq``, or one past the sequence length. Its "type" is the set ``1..Len(seq)+1``. Similarly, we know ``seen`` can't have any values not in ``S``. Expanding our type invariant:

::

  TypeInvariant ==
    /\ is_unique \in BOOLEAN
    /\ seen \subseteq S
    /\ i \in 1..Len(seq)+1

I think that's enough of an introduction to invariants. Now let's write one that proves our algorithm correct.

.. index:: duplicates

Testing Duplicates
-------------------

When the algorithm finishes, ``is_unique`` is either true or false. If it's true, then every indice of the value is unique. If it's false, then there must be duplicates. So we're looking at something like

::

  IsCorrect == IF is_unique THEN IsUnique(seq) ELSE ~IsUnique(seq)

We can simplify this by just using ``=``.

::

  IsCorrect == is_unique = IsUnique(seq)

Now the next two steps:

1. Actually implement ``IsUnique(s)``.
2. Currently, ``is_unique`` starts out true and flips to false if we find a duplicate. If the sequence *isn't* unique, then the invariant would fail as soon as we start— ``is_unique`` is true but ``IsUnique(seq)`` will be false. So we only want to check the "invariant" after the algorithm finishes running.

Writing ``IsUnique(s)`` *properly* requires learning some things. Writing it *improperly* is pretty easy though, so let's stat with that, then cover (2), the double back to doing ``IsUnique`` properly.

Here's the improper solution for ``IsUnique``:

::

  IsUnique(s) == Cardinality(seen) = Len(s) 

If the sequence has duplicates, then we won't run the ``\union`` line every single time, so it will have a different cardinality. In the next section, we'll see why this is "improper" and implement it properly, but for now this opens up our ability to discuss (2).

.. note:: This works because sets are unique.


.. index:: pc
.. _pc:

pc
....

Time for a quick leaky abstraction. We talk about the labels as being the units of atomicity. That's a PlusCal abstraction to help developers. These are translated to the "actions" in TLA+. To track the label, the PlusCal translator adds an additional variable called ``pc``. The value of ``pc`` is a string matching the name of the current label we evaluated.

You can see this in the error trace. When we start the algorithm, ``pc = "Iterate"``. After the algorithm completes, ``pc = "Done"``. So we can only test our invariant at the end with

::

  IsCorrect == IF pc = "Done" THEN is_unique = IsUnique(seq) ELSE TRUE

On every label *except* "Done", this evaluates to TRUE and the invariant passes. When it *is* "Done", then we check the condition we care about.

.. index:: => (implies)

``IF A THEN B ELSE TRUE`` conditionals come up a lot, cases where we only want to check B if A is true. Another way of saying this "either B is true or A is false".

Another way of writing this: ``A => B``. Either B is true or A is false. Now we have

::

  IsCorrect == pc = "Done" => is_unique = IsUnique(seq)

I said ``=>`` was really important earlier. This is one of those ways: it lets us say invariants should only apply under certain conditions. 

We can now run this as our full invariant, and the spec works :ss:`duplicates_many_inputs`. 

.. _\A:
.. _\E:
.. _quantifiers:

Quantifiers
===================

.. note:: If you've been working in your own spec, I recommend switching to `scratch` for now, since we'll be testing a lot of simple operators. 

Here's our current version of ``IsUnique``.

::

  IsUnique(s) == Cardinality(seen) = Len(s) 

I said that this is the improper way. That's for two reasons. First of all, it's tying the definition of uniqueness to ``seen``, which is a variable. Whether a sequence is unique or not should be independent of our actual behavior. It is or it isn't. The ``IsUnique`` operator should rely on the values in ``s`` and nothing else.

Second, this isn't really the *definition* of uniqueness. We're just using a clever trick involving set cardinalities. It'd be better if we our operator captured the meaning of uniqueness, not a weird side-channel which is coincidentally identical to uniqueness. 

Finally, this doesn't give us anywhere to go. We could represent uniqueness this way, but what about, say, sortedness? 

For all these reasons, it's time to introduce :dfn:`quantifiers`. A quantifier is a statement about the elements in a set. There are two: ``\A``, or "forall", tests if a statement is true about *every* element in the set. ``\E``, or "exists", tests if it's true for *at least one* element. If I write

::

  \A x \in {1, 2, 3}: x < 2

That's equivalent to "every element in the set is less than 2", which is false. If I wrote ``\E x \in {1, 2, 3}: x < 3``, that would instead be true.

.. warning:: 

  ``\A x \in {}: ...`` is always true, and ``\E`` is always false. All zero elements satisfy the statement, while not one does! In fact, this is the only case where "forall" can be true when "exists" is not.

We can pull multiple elements from the same quantifier. Example: a *composite* number is divisible by a number besides one and itself. I can write ``IsComposite`` as

::

  IsComposite(num) ==
    \E m, n \in 2..Len(num):
      m * n = num

Notice that m and n can be the same number: ``IsComposite(9) = TRUE`` when we pick ``m = n = 3``.

.. tip::

  You can also pull from several *different* sets in the same quantifier: ``\A x \in S, y \in T: P(x, y)``.


We can't use a quantifier on a sequence, since that's not a set. But we *can* use it on the sequence's indices.

::

  Contains(seq, elem) ==
    \E i \in 1..Len(seq):
      seq[i] = elem

That suggests we can write ``IsUnique`` as

::

  IsUnique(s) ==
  \* Warning, this is wrong!
  \* We'll see why in the next part.
    \A i, j \in 1..Len(s):
      s[i] # s[j]



.. index:: => (implies)


The power of :math:`\Rightarrow`
---------------------------------

Let's add this new version of ``IsUnique`` to our duplicates spec:

.. spec:: duplicates/inv_3/duplicates.tla
  :diff: duplicates/inv_2/duplicates.tla
  :fails:

If you run this, you will see it *fail*. And it fails in the oddest way, by saying a unique sequence has duplicates. In my case I got ``seq = <<1, 2, 3, 4>>``, but the exact one TLC finds may differ on your computer.

Let's use `CHOOSE` to ask TLC *what* indices it picked. Back in `scratch`:

::

  Eval == LET
    seq == <<1, 2, 3, 4>>
    s == 1..4
  IN
    CHOOSE p \in s \X s: seq[p[1]] = seq[p[2]]

  >>> Eval
  <<1, 1>>

**We never said the indices had to be different.** Obviously every index is going to be equal to itself!

Here's one way to fix it:

::

  IsUnique(s) ==
    \A i \in 1..Len(s):
      \A j \in (1..Len(s)) \ {i}:
        s[i] # s[j]

That… works, I guess. But there's a better way to do this, one that really showcases the power of ``=>``: **it lets us rule out unwanted combinations in quantifiers.** Let's say we write

::

  IsUnique(s) ==
    \A i, j \in 1..Len(s):
      i # j => s[i] # s[j]

Then we pass in ``<<"a", "b">>``. There are four possible combinations of values for i and j. Let's write out the full truth table for every combination:

.. list-table::
  :header-rows: 1

  * - ``i, j``
    - ``s[i], s[j]``
    - ``i # j (P)`` 
    - ``s[i] # s[j] (Q)``
    - ``P => Q``
  * - 1, 1
    - a, a
    - F
    - F
    - **T**
  * - 1, 2
    - a, b
    - T
    - T
    - **T**
  * - 2, 1
    - b, a
    - T
    - T
    - **T**
  * - 2, 2
    - b, b
    - F
    - F
    - **T**

For every combination, ``P => Q`` is true. This means the ``\A`` is true, and ``IsUnique(<<a, b>>)``, as expected.

Now let's do the same for ``<<a, a>>``:

.. list-table::
  :header-rows: 1

  * - ``i, j``
    - ``s[i], s[j]``
    - ``i # j (P)`` 
    - ``s[i] # s[j] (Q)``
    - ``P => Q``
  * - 1, 1
    - a, a
    - F
    - F
    - **T**
  * - 1, 2
    - a, a
    - T
    - F
    - **F**
  * - 2, 1
    - a, a
    - T
    - F
    - **F**
  * - 2, 2
    - a, a
    - F
    - F
    - **T**

Since ``1, 2`` gives us ``T => F``, there's a case where the quantiifer fails, and ``~IsUnique(<<a, a>>)``, as we want it to be. ``=>`` is an *incredibly* powerful tool for writing invariants. 

So we just make that change, and:

.. spec:: duplicates/inv_4/duplicates.tla
  :diff: duplicates/inv_3/duplicates.tla

This should pass :ss:`duplicates_many_inputs`.

.. warning:: Do not use ``=>`` with ``\E``! Imagine I wanted to an operator that checks if a sequence has duplicates, and wrote

  ::

    HasDuplicates(seq) ==
      \E i, j \in 1..Len(seq):
        i # j => seq[i] = seq[j]

  If I picked ``i = j = 1``, then the left-hand side would be false, meaning the expression is true, meaning the whole quantifier is true. *This holds regardless of the right-hand side!* Instead I should write

  ::

    HasDuplicates(seq) ==
      \E i, j \in 1..Len(seq):
        i # j /\ seq[i] = seq[j]

.. todo::

  .. rubric:: More invariant practice

  .. todo:: Find actual names for everything

  Consider we have an event queue of events that happen in a system, where the queue is represented by a sequence of strings. One of teh invariants of the system is that "A can only come after B if the D flag is set."

  Properties of the form "X can only be true if Y is also true" can be written as ``X => Y``. To see why, try writing out the truth table.

  So we have:

  ::

    Inv == IsAfter(A, B) => D

  That just leaves specifying ``IsAfter``. 

  ::

    \* Test this

    IsAfter(seq, e1, e2) ==
      \E i, j \in 1..Len(seq):
        /\ i > j
        /\ seq[i] = e1
        /\ seq[j] = e2


  .. todo:: 

    .. rubric:: More invariant practice

    ``=>`` is extremely powerful, so let's spend more time working with it. How would we write an operator that tests if a sequence is sorted in ascending order? What would ``IsSorted(seq)`` look like

    ::

      IsSorted(seq) ==
        \A i, j \in 1..Len(seq):
          i < j => seq[i] <= seq[j]


When to use Invariants
=======================

.. todo::

  The invariant we wrote here, "the algorithm has the correct answer at the end", isn't usually written *as an invariant*. There's a more elegant way to specify that, which we'll be covering in a `later chapter <chapter_temporal_logic>`.

  Invariants are your bread and butter of TLA+. Every specification should at least have a type invariant, to make sure all values are what you expect. They are very cheap to check. Use a lot of them. Here are some invariants I've written for production specs:


  - Messages on the queue are unique.
  - 


Summary
========

* Invariant
* Type Invariants
* Implication
* Quantifiers
* More implication
* When to use invariants
