.. _chapter_functions:

++++++++++++++
Functions
++++++++++++++

In this chapter we will cover

* Structures
* Functions
* Function sets


.. _struct:

Structures
============

Sequences cover tuples and arrays, now we need something to represent string hashmaps. In TLA+, this is the struct:

::

  struct == [a |-> 1, b |-> {}]


You index structs the same way you do sequences so ``struct["a"] = 1``. You can also write it in a more "object" like with a dot instead: ``struct.a = 1``.

.. troubleshooting::

  Quoted keys


Unsurprisingly, structs are mainly used to represent organized collections of data. For example, a TK might consist of an TK.

.. some kind of exercise

Just like sequences, sets, and primitive values, we want some way to generate sets of structs, so we can stick them in our type invariants. Here's how:

::

  StructType == [a: S, b: T] \* make better

This is the set of all structures where ``s.a \in S /\ s.b \in T``.

.. _domain:

DOMAIN
--------

If I wanted to find all of the values of a *sequence*, I could get it like this:

::

  RangeSeq(seq) == {seq[i]: i \in 1..Len(seq)]

How can I get all the values of a structure? ``Len`` isn't defined for structures. Instead, we have the special keyword ``DOMAIN``. ``DOMAIN struct`` is the set of all keys of a structure.

::

  RangeStruct(struct) == {seq[key]: key \in DOMAIN struct}

Try this out.

Now for the fun bit. What happens if we pass a *sequence* into ``RangeStruct``?

::

  >>> RangeStruct(<<"a", "b", "a">>)

  {"a", "b"}

...Huh. ``DOMAIN seq == 1..Len(seq)``! In fact, it's actually *the other way around*: ``Len`` is defined in terms of DOMAIN!

.. exercise:: MyLen
  :label: mylen

  Write ``MyLen(seq)``, which returns the length of seq, without using ``Len``. You may need ``Max(set)``.

  .. Max(DOMAIN seq)

Here's the punchline: *both sequences and structures are just syntactic sugar*. TLA+ has only two "real" collections: sets and functions. Sequences and structures are both particular classes of functions, the ones that we as programmers are most familiar with. It's time to finally introduce the true data type.


.. _functions:
.. _function:

Functions
===============

First of all, throw away the programming definition of "function". The closest thing TLA+ has to a programmatic function are operators. A :dfn:`function` follows the *mathematical* definition, a mapping of values in one set to another set.

::

  F == [x \in S |-> expr]

The set we're mapping from, ``S``, is the :dfn:`domain` of the function, and can be retreived by writing ``DOMAIN F``. That's why we could also use ``DOMAIN`` with sequences and structures:

1. A sequence is a function with domain ``1..n``.
2. A struct is a function with a domain of strings.

But functions are a more general than that, and can map *any* set of values. For example, we can have pairs of numbers in the domain of the function.

::
  
  Prod == 
    LET S == 1..10 IN
    [p \in S \X S |-> p[1] * p[2]]

  \* Prod[<<3, 5>>] = 15

.. tip::

  You can also write that as ``Prod == [x \in S, y \in S |-> x * y]``, or ``G == [x, y \in S |-> x * y]``. You can also call the function with ``Prod[3, 5]`` and leave out the angle brackets. 

  (Internally, TLA+ will represent it as a tuple, so ``DOMAIN F = S \X T``.)

.. exercise::

  Write ``Double(seq)``.

  ::

    Double(<<1, 2, 3>>) = <<2, 4, 6>>

  .. 

.. todo:: 

  Explain truth tables, then find the truth table of something simple.

  ::

    TruthTable == [p \in BOOLEAN, q \in BOOLEAN |-> p => q]

  Exercise: truth table of something super complex


@@ and :>
...........

TODO

Using Functions
-----------------

Why functions over operators? We rarely use functions for computations— operators are far superior for that. Functions are important as *values*. We can assign them to variables and manipulate them like any other value.

.. todo:: make the below a spec

::

  People == {"alice", "bob", "carol"}


  (*--algorithm example
  variables
    acct = [p \in People |-> 10];
    from \in People;
    to \in People;
  begin
    A:
      acct[from] := acct[from] - 1;
    B:
      acct[to] := acct[to] + 1;
  end algorithm; *)

.. note:: THis will make a lot more sense once we've covered concurrency.

.. exercise::

  Write invariants on the functions

.. _function_set:
.. _function_sets:

Function sets
----------------

You know the drill by now: new class of value, new need for a way to generate sets of that value. We need to add function values to our type invariants, too!

The syntax for function sets is ``[S -> T]`` and is "every function where the domain is ``S`` and all of the values are in ``T``." Some examples: 

#. We're tracking ownership of items by people: ``owns[i] = p`` means that person ``p`` is the owner of item ``i``. No matter what the assignments, ``owns \in [Item -> Person]``.
#. We have a set of servers, which can have one of three states. Then ``status \in [Server -> {"online", "booting", "offline"}]``.
#. We represent a directed graph as a function on pairs of points, which is true iff there's an edge between the two points. Then ``graph \in [Node \X Node -> BOOLEAN]``.
#. If we define the previous set as the operator ``GraphType``, we could get the set of all *undirected* graphs with ``{g \in GraphType: \A n1, n2 \in Node: g[n1,n2] = g[n2,n1]}``.
#. Integer addition, as in "two plus two is four", is an element of the function set ``[Int \X Int -> Int]``. However, while this is expressible, TLC cannot enumerate this set.

.. troubleshooting::

  If you get

  X

  You probably wrote ``[S |-> T]`` instead of ``[S -> T]``. Similarly, if you get

  Y

  You probably wrote ``[x \in S -> T]`` instead of ``[x \in S |-> T]``. Don't worry, everybody gets the two mixed up at some point.

.. exercise::

  Given the sets ``Servers`` and ``StatusType == {"on", "off", "booting"}``, find the set of all status configurations where at least one server is booting.

  ::

    {config \in [Servers -> StatusType]: \E s \in Servers: config[s] = "booting"}

  .. this is too hard

.. index:: duplicates

The Duplicate Checker Again
...........................

*You will never be free of this*

Our last version of the duplicate checker was this:

.. spec:: duplicates/inv_4/duplicates.tla

If I wanted to try it on five-element sequences, I'd have to add another ``\X S``. By the time we hit six or seven elements, it's too unwieldy to work with. 

We can simplify this with function sets. ``S \X S \X S`` is going to be a set of 3-tuples. We now know that a 3-tuple is a function with domain ``1..3``. Then ``[1..3 -> S] = S \X S \X S``: the set of all 3-tuples where each element of each tuple is a value in ``S``.

From this, extending this to five-element sequences is trivial :ss:`duplicates_len_5_seqs`:

.. spec:: duplicates/fs_1/duplicates.tla
  :diff: duplicates/inv_4/duplicates.tla

Notice now that, while ``S \X S \X S`` has a *hardcoded* length, ``[1..3 -> S]`` is based on a *value* — the size of the domain set. We can base that value on a variable, too!

.. spec:: duplicates/fs_2/duplicates.tla
  :diff: duplicates/fs_1/duplicates.tla


Now, instead of checking all length 5 sequences, we're checking all length 5 *or smaller* sequences :ss:`duplicates_len_5_or_less`! This is a useful specifying trick known as *state sweeping*.

.. technique:: State Sweeping

  *State sweeping* is when we use an initial starting state variable to control the parameters for other variables. For example, we could have one variable determine the length of an input sequence, or the maximum size of a bounded buffer.

  Strictly speaking, sweeping isn't *necessary*: we can, with sufficient cleverness, construct a complex operator that does the same thing. Sweeping, however, is often much *easier* than doing that, and frees up your brainpower for the actual act of specification.


.. exercise::

  TODO

Summary
===========

TODO
