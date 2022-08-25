.. _chapter_functions:

+++++++++++++++
Structured Data
+++++++++++++++


.. _struct:

Structures
============

Sequences cover tuples and arrays, now we need something to represent string hashmaps. In TLA+, this is the struct:

::

  struct == [a |-> 1, b |-> {}]


You index structs the same way you do sequences so ``struct["a"] = 1``. You can also write it in a more "object" like with a dot instead: ``struct.a = 1``.

.. troubleshooting::

  If you get

    Encountered "\|->" at line X, column Y and token "key"

  It's because you wrote ``["key" |-> val]`` instead of ``[key |-> val]``.


Unsurprisingly, structs are mainly used to represent organized collections of data. For example, a ``BankTransaction`` might consist of an account, an amount, and whether it was a deposit or withdrawal.

Just like sequences, sets, and primitive values, we want some way to generate sets of structs, so we can stick them in our type invariants. Here's how:

::

  \* Accounts is a set of model values
  BankTransactionType == [acct: Accounts, amnt: 1..10, type: {"deposit", "withdraw"}]

This is the set of all structures where ``s.acct \in Accounts``, ``s.amnt \in 1..10``, etc.

.. tip:: With complex types especially, it's good idea to regularly estimate how many elements are in the set. Here, for in a model with three accounts, BankTransactionType will have :math:`3 \cdot 10 \cdot 2 = 60` elements.

.. troubleshooting::

  If you get

    Attempted to compute the number of elements in the string "val"

  *at model-checking time*, it's because you wrote ``[key: "val"]`` instead of ``[key: {"val"}]``.



.. index:: DOMAIN
.. _DOMAIN:

Getting a Struct's Keys
-----------------------

If I wanted to find all of the values of a *sequence*, I could get it like this:

::

  RangeSeq(seq) == {seq[i]: i \in 1..Len(seq)}

How can I get all the values of a structure? ``Len`` isn't defined for structures. Instead, we have the special keyword ``DOMAIN``. ``DOMAIN struct`` is the set of all keys of a structure.

::

  RangeStruct(struct) == {struct[key]: key \in DOMAIN struct}

Now for the fun bit. What happens if we pass a *sequence* into ``RangeStruct``?

::

  >>> RangeStruct(<<"a", "b", "a">>)

  {"a", "b"}

It looks like ``DOMAIN seq == 1..Len(seq)``! In fact, it's actually *the other way around*: ``Len`` is defined in terms of ``DOMAIN``!

Here's the punchline: *both sequences and structures are just syntactic sugar*. TLA+ has only two "real" collections: sets and functions. Sequences and structures are both particular classes of functions, the ones that we as programmers are most familiar with. It's time to finally introduce the true data type.

.. index:: function, types; function

.. _functions:
.. _function:

Functions
===============

First of all, throw away the programming definition of "function". The closest thing TLA+ has to a programmatic function are operators. A function follows the *mathematical* definition, a mapping of values in one set to another set.

::

  F == [x \in S |-> expr]

The set we're mapping from, ``S``, is the **domain** of the function, and can be retreived by writing ``DOMAIN F``. That's why we could also use ``DOMAIN`` with sequences and structures:

1. A sequence is just a function where the domain is ``1..n``.
2. A struct is just a function where the domain is a set of strings.

But functions are a more general than that, and can map *any* set of values. For example, we can have pairs of numbers in the domain of the function.

::
  
  Prod == 
    LET S == 1..10 IN
    [p \in S \X S |-> p[1] * p[2]]

  \* Prod[<<3, 5>>] = 15

.. tip::

  You can also write that as ``Prod == [x \in S, y \in S |-> x * y]``, or ``G == [x, y \in S |-> x * y]``. You can also call the function with ``Prod[3, 5]`` and leave out the angle brackets. 

  (Internally, TLA+ will represent it as a tuple, so ``DOMAIN F = S \X T``.)

I like using functions to show me the results of an expression for various inputs. For what values of P and Q is ``P => Q`` true?

  ::

    TruthTable == [p, q \in BOOLEAN |-> p => q]

If you run this in `scratch <scratch>`, you'll get the results, though they'll be in an unusual format:

.. code-block:: text

  >>> TruthTable

  ( <<FALSE, FALSE>> :> TRUE @@
  <<FALSE, TRUE>> :> TRUE @@
  <<TRUE, FALSE>> :> FALSE @@
  <<TRUE, TRUE>> :> TRUE )

.. index:: @@ (merge), :> (map function)

This is in "expanded form": ``x :> y`` is the single-valued function mapping x to y (so ``[s \in {x} |-> y]``), and ``@@`` merges two functions. If the two functions share a key, then ``@@`` **keeps the value on the left**.

.. note:: ``@@`` and ``:>`` are only available in your spec if you extend ``TLC``.

With this, `we can see <scratch>` how sequences and structures are just functions:

.. code:: none

  >>> 1 :> "a" @@ 2 :> "b" 
  <<"a", "b">>

  >>> "a" :> 1 @@ "b" :> 2
  [a |-> 1, b |-> 2]

.. rubric:: Example: Zip

Python has a function called ``zip``. It takes two iterables and returns a single sequence, where the elements are pairs of elements from the two inputs. If one is larger than the other, it only does up to the length of the shorter.

.. code:: python

  >>> list(zip([1, 2], ["a", "b", "c"]))
  [(1, 'a'), (2, 'b')]

Normally programming languages implement zip with iteration or recursion. We don't need that here because we can "see" the entire sequence at once.


::

  Zip1(seq1, seq2) ==
    LET Min(a, b) == IF a < b THEN a ELSE b
        N == Min(Len(seq1), Len(seq2))
    IN
      [i \in 1..N |-> <<seq1[i], seq2[i]>>]

Another way we could write this would be to notice that the `intersection <set_operators>` of ``1..a`` and ``1..b`` is ``1..Min(a,b)``. So we can simplify ``Zip`` to:

::

  Zip2(seq1, seq2) ==
    LET N == (DOMAIN seq1) \intersect (DOMAIN seq2)
    IN
      [i \in N |-> <<seq1[i], seq2[i]>>]

We can check that these are equivalent by writing a quantifier check:

::

  LET 
    S == 1..4
    Input == (S \X S \X S) \union (S \X S)
  IN
    \A s1, s2 \in Input:
      Zip1(s1, s2) = Zip2(s1, s2)

Using Functions
-----------------

Why functions over operators? We rarely use functions for computations— operators are far superior for that. Functions are important as *values*. We can assign them to variables and manipulate them like any other value.

In a spec I once wrote, I had to assign tasks to CPUs. Some tasks needed to be assigned to many CPUs, but each CPU should only have one task. In that spec, the best solution was to store assignments as functions, where each task mapped to a set of CPUs.

::

  variables
    assignments = [t \in Tasks |-> {}] 

Then I could write ``assignment[t] := assignment[t] \union {cpu}`` to assign ``cpu`` to task ``t``. For my invariant, I said no two tasks shared a CPU assignment.

::

  OnlyOneTaskPerCpu ==
    \A t1, t2 \in Tasks, c \in CPU:
      /\ (t1 # t2) 
      /\ c \in assignments[t1] 
      => c \notin assignments[t2]

We could also write this invariant by noticing that "tasks don't share cpus" is the same as saying "assignment sets are disjoint":

::

  OnlyOneTaskPerCpu ==
    \A t1, t2 \in Tasks:
      (t1 # t2) 
      => assignments[t1] \intersect assignments[t2] = {}

.. index:: function; function sets, sets of; functions, [A -> B]

.. _function_set:
.. _function_sets:

Function sets
----------------

You know the drill: new class of value, new need for a way to generate sets of that value. We need to add function values to our type invariants, too!

The syntax for function sets is ``[S -> T]`` and is "every function where the domain is ``S`` and all of the values are in ``T``." [#codomain]_ In the prior task example, ``assignments`` was always a function in the function set ``[Tasks -> SUBSET CPUs]``.

.. tip:: A function set of form ``[A -> B]`` will have :math:`\#B^{\#A}` elements in it. If there were two tasks and three CPUs, that would be :math`(2^3)^2 = 64` possible functions.

  A good way to remember this: ``[1..n -> BOOLEAN]`` is the set of all binary strings of length ``n``, and we know there are :math:`2^n` such strings.

I can also use `set maps <map>` and filters here. Let's say a task can only be assigned to at most two CPUs. If I wanted to, I could fold that into the type invariant, using a function set::

  TypeInvariant ==
    \* ...
    /\ assignments \in 
      LET LeqTwoCPUs == {set \in SUBSET CPUs: Cardinality(set) <= 2}
      IN [Tasks -> LeqTwoCPUs]

Though in this case I'd prefer to keep the type invariant simple and write a second invariant with the additional restriction::

  TypeInvariant ==
    /\ assignments \in [Tasks -> SUBSET CPUs]

  AnotherInvariant ==
    \A t \in Tasks: Cardinality(assignments[t]) <= 2

Some more examples of function sets: 

#. We have a set of servers, which can have one of three states. Then ``status \in [Server -> {"online", "booting", "offline"}]``.
#. We represent a directed graph as a function on pairs of points, which is true iff there's an edge between the two points. Then ``graph \in [Node \X Node -> BOOLEAN]``.
#. If we define the previous set as the operator ``GraphType``, we could get the set of all *undirected* graphs with ``{g \in GraphType: \A n1, n2 \in Node: g[n1,n2] = g[n2,n1]}``.
#. If we have a set of users and resources, the set of all possible allocations could be ``[Resource -> User]``. If some resources could be unallocated, it would instead be ``[Resource -> User \union {NULL}]`` (where NULL is a `model value <model_value>`.


.. troubleshooting::

  If you get

    Encountered "\|->" in line X, column Y

  In a function set, then you probably wrote ``[S |-> T]`` instead of ``[S -> T]``. Similarly, if you get

    Encountered "->" in line X, column Y

  In a function, then you probably wrote ``[x \in S -> T]`` instead of ``[x \in S |-> T]``. Don't worry, everybody gets the two mixed up at some point.

.. rubric:: Example: Sorting

Let's put function sets to good use. If we want to test if a sequence is sorted in ascending order, we can write it like this: 

::

  IsSorted(seq) ==
    \A i, j \in 1..Len(seq):
      i < j => seq[i] <= seq[j]

Now what about an operator that *sorts* as a sequence? Specifically, one such that ``IsSorted(SortSeq(seq))`` is always true. That's easy:

::

  Sort(seq) ==
    <<>>

We had to tweak the definition a bit and make sure that the output sequence has all the same elements, too. 

Now you might remember from our discussion of `CHOOSE` that instead of manually constructing the sequence with the desired properties, it's easier to instead take a set of sequences and pluck out the one that has the properties we want.

We know we can get the set of elements in a sequence this way:

::
  
  Range(f) == {f[x] : x \in DOMAIN f}

Then ``[DOMAIN seq -> Range(seq)]`` is the set of all sequences which have the same elements as ``seq``. Our operator will then look something like this:

::

  Sort(seq) ==
    CHOOSE sorted \in [DOMAIN seq -> Range(seq)]:
      /\ \* sorted has the same number of each element as seq
      /\ IsSorted(sorted)

To figure out if two sequences have the same number of each element, let's define a ``CountMatching(f, val)`` operator that tells us the number of inputs matching ``val``. To get the size of a set, we need `Cardinality <Cardinality>` from the ``FiniteSets`` module.

::

  CountMatching(f, val) ==
    Cardinality({key \in DOMAIN f: f[key] = val})
    
Then we just need to test to check this over every element in the sequence:

::

  Sort(seq) ==
    CHOOSE sorted \in [DOMAIN seq -> Range(seq)]:
      /\ \A i \in DOMAIN seq:
        CountMatching(seq, seq[i]) = CountMatching(sorted, seq[i])
      /\ IsSorted(sorted)

Let's try this on some input:

::

  >>> Sort(<<8, 2, 7, 4, 3, 1, 3>>)
  <<1, 2, 3, 3, 4, 7, 8>>

Perfect!

.. index:: duplicates

The Duplicate Checker Again
===========================

Last time, I promise.

Our last version of the duplicate checker was this:

.. note:: ``S <- 1..10`` for all these examples.

.. spec:: duplicates/constant_2/duplicates.tla

Currently we can control the value of ``S`` per model, it would be good if we could control the length of ``seq`` too. Then we can test both 2-element sequences and 20-element sequences. But currently the length is hardcoded by the number of ``\X`` cross-products we used.

We can simplify this with function sets. ``S \X S \X S`` is going to be a set of 3-tuples. We now know that a 3-tuple is a function with domain ``1..3``. Then ``[1..3 -> S] = S \X S \X S``: the set of all 3-tuples where each element of each tuple is a value in ``S``.

From this, extending this to five-element sequences is trivial:

.. spec:: duplicates/fs_1/duplicates.tla
  :diff: duplicates/constant_2/duplicates.tla
  :ss: duplicates_len_5_seqs

Notice now that, while ``S \X S \X S`` has a *hardcoded* length, ``[1..3 -> S]`` is based on a *value* — the size of the domain set. This means we can pull it into a constant!

.. spec:: duplicates/fs_2/duplicates.tla
  :diff: duplicates/fs_1/duplicates.tla

.. _state_sweeping:

.. tip::

  *State sweeping* is when we use an initial starting state variable to control the parameters for other variables. For example, we could have one variable determine the length of an input sequence, or the maximum size of a bounded buffer.

  .. spec:: duplicates/fs_3/duplicates.tla
    :diff: duplicates/fs_2/duplicates.tla
    :ss: duplicates_len_5_or_less

  Now, instead of checking all length 5 sequences, we're checking all length 5 *or smaller* sequences! This is a useful specifying trick known as *state sweeping*.

  Strictly speaking, sweeping isn't *necessary*: we can, with sufficient cleverness, construct a complex operator that does the same thing. Sweeping, however, is often much *easier* than doing that, and frees up your brainpower for the actual process of specification.


Summary
===========

* Functions map a set of values to another set of values. They are written ``[x \in set |-> Expr(x)]`` and called with ``f[value]``.

    * Functions can also be written ``[x, y \in Set1, z \in Set2 |-> P(x, y, z)`` and called with ``f[a, b, c]`` (or ``f[<<a, b, c>>]``).

* The domain of a function, the set we're mapping from, is ``DOMAIN f``.

    * ``a :> b`` is the function ``[x \in {a} |-> b]``.
    * ``f @@ g`` merges ``f`` and ``g``, **preferring keys in f**.

* Sequences are just a special kind of function, where the domain is ``1..n``. 
* Structures are another special kind of function, written ``[key1 |-> val1, key2 |-> val2]``. They are called with ``struct["key1"]`` (or ``struct.key1``).
* Functions and structures both have special set syntax. For structures, it is ``[key1: set1]``. For functions, it's ``[A -> B]``.

.. [#codomain] T is sometimes referred to as the "codomain".
