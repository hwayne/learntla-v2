.. _reference_standard_modules:

+++++++++++++++++++
Standard Modules
+++++++++++++++++++

.. all from https://github.com/tlaplus/tlaplus/tree/master/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules

This only includes models that are usable by TLC. Reals and RealTime are not covered.

.. todo:: something about overrides

Naturals
============

Defines ``+ - * ^ % < > <= >=`` as well as

Nat
  The set ``{0, 1, ...}``. |noenumerate|

``a..b``
  The set ``{a, a + 1, ..., b}``.

``a \div b``
  Floor division: ``10 \div 3 = 3``.

Integers
============

Defines everything in ``Naturals`` as well as 

Int
  The set of all integers. |noenumerate|

-a
  Negative numbers.

Sequences
============

Required for `pluscal procedures <procedure>`. A sequence is like a list in any other language. You write it like ``<<a, b, c>>``, and the elements can be any other values (including other sequences).
Check the related section on :doc:`sequences </core/operators>`.

Seq(set)
  The set of all sequences where the values are all elements of ``set``. TLC has special code to check if you're testing membership, this is not memory/cpu intensive. |noenumerate|

  ::  

    <<a>>          \in Seq({a, b})
    <<a, b>>       \in Seq({a, b})
    <<a, b, b, a>> \in Seq({a, b})
    \* in practice, the output is a set that contains all sequences made from 'a's and 'b's, 
    \* so it also includes the sequence <<a, a, a, a, b, a, b>> for example. That's why it's nonenumerable.

Len(seq)
  Length of ``seq``.

  ::

    Len(<<2, 4, 6>>) = 3

Head(seq)
  First element of ``seq``.

  ::

    Head(<<1, 2, 3>>) = 1

Tail(seq)
  All but first element of ``seq``.

  ::

    Tail(<<1, 2, 3>>) = <<2, 3>>


``seq1 \o seq2``
  Concatenates two sequences.

  ::

    <<1>> \o <<2 , 3>> = <<1, 2, 3>>

Append(seq, e)
  Append ``e`` at the end of ``seq``. Equivalent to ``seq1 \o <<e>>``.

  ::

    Append(<<1, 2>>, 3) = <<1, 2, 3>>
  
SubSeq(seq, m, n)
  Used to select the subsequence ``<<s[m], s[m+1], ... , s[n]>>`` in seq. Indices are inclusive. |fromdocs|

  ::

    SubSeq(<<7, 8, 9>>, 1, 2) = <<7, 8>>

SelectSeq(seq, Op(_))
  Sequence filter using Op.

  ::

    IsEven(x) == x % 2
    SelectSeq(<<1, 2, 3>>, IsEven) = <<2>>

FiniteSets
============

IsFiniteSet(set)
  Tests if ``set`` is not an infinite set.

  ::

    IsFiniteSet({2, 5, 7}) = TRUE
    IsFiniteSet(Seq({1})) = FALSE
    IsFiniteSet(Nat) = FALSE

Cardinality(set)
  The number of elements in ``set``.

  ::

    Cardinality({2, 5, 7}) = 3

.. _bag:

Bags
============

Also known as multisets. Bags are functions items to "counts" of items. IE the struct ``[a |-> 1, b |-> 2]`` is a bag. The values of a bag must be positive integers.

IsABag(func)
  Tests if ``func`` is a bag.

  ::

    IsABag([a |-> 3, b |-> 7]) = TRUE

BagToSet(bag)
  Equivalent to ``DOMAIN bag``.

  ::

    BagToSet([a |-> 3, b |-> 7]) = {"a", "b"}

SetToBag(set)
  Equivalent to ``[x \in set |-> 1]``.

  ::

    SetToBag({}) = <<>>
    SetToBag({"a","b"}) = [a |-> 1, b |-> 1]
    SetToBag({"a", "b", "a", "a"}) = [a |-> 1, b |-> 1]

BagIn(e, bag)
  Equivalent to ``e \in DOMAIN bag``.

  ::

    BagIn("a", [a |-> 1, b |-> 1]) = TRUE
    BagIn("c", [a |-> 1, b |-> 1]) = FALSE

EmptyBag
  Equivalent to ``<<>>``.

  ::

    EmptyBag = <<>>

``bag1 (+) bag2``
  Bag addition. Creates a new bag where each key is the sum of the values of that key in each bag.

  ::

    [a |-> 1, b |-> 3] (+) EmptyBag = [a |-> 1, b |-> 3]
    [a |-> 1, b |-> 3] (+) [a |-> 1] = [a |-> 2, b |-> 3]
    [a |-> 1, b |-> 3] (+) [c |-> 1] = [a |-> 1, b |-> 3, c |-> 1]

``bag1 (-) bag2``
  Bad subtraction. If ``bag2[e] >= bag1[e]``, then ``e`` is dropped from the final bag's keys.

  .. todo:: Topic of a bag that goes Nat instead of Nat-0
  
  ::

    \* Nothing changes:
    [a |-> 1, b |-> 3] (-) EmptyBag = [a |-> 1, b |-> 3]
    \* a is removed from the bag:
    [a |-> 1, b |-> 3] (-) [a |-> 1] = [b |-> 3]
    \* a is decreased by the amount of the second bag:
    [a |-> 2, b |-> 3] (-) [a |-> 1] = [a |-> 1, b |-> 3]
    \* c is not in the domain of the bag on the left, hence nothing changes:
    [a |-> 1, b |-> 3] (-) [c |-> 1] = [a |-> 1, b |-> 3]


BagUnion(set)
  Equivalent to ``bag1 (+) bag2 (+) ...``, where ``set = {bag1, bag2, ...}``.

  ::

    BagUnion({}) = <<>>
    BagUnion({[a |-> 2]}) = [a |-> 2]
    BagUnion({[a |-> 2], [b |-> 3]}) = [a |-> 2, b |-> 3]


``B1 \sqsubseteq B2``
  B1 \sqsubseteq B2 iff, for all e in DOMAIN B1, bag B2 has at least as many copies of e as bag B1 does. |fromdocs| 
  
  ::

    [a |-> 2, b |-> 3] \sqsubseteq [b |-> 2] = FALSE
    [a |-> 2, b |-> 3] \sqsubseteq [a |-> 2, b |-> 2] = FALSE
    [a |-> 2, b |-> 3] \sqsubseteq [a |-> 2, b |-> 3] = TRUE
    \* it doesn't matter if B2 has "c |-> 1", because has enough copies of a and b.
    [a |-> 2, b |-> 3] \sqsubseteq [a |-> 2, b |-> 3, c |-> 1] = TRUE
    [a |-> 2, b |-> 3] \sqsubseteq [a |-> 5, b |-> 3, c |-> 1] = TRUE

SubBag(bag)
  The set of all subbags of ``bag``.

  ::

    SubBag(EmptyBag) = {<<>>}
    SubBag([a |-> 2]) = {<<>>, [a |-> 1], [a |-> 2]}

BagOfAll(Op(_), bag)
  If ``bag[e] = x``, then ``out[Op(e)] = x``. eg

  ::

    b == <<1, 3, 5>>
    >>> BagOfAll(LAMBDA x: x^2, b)

    (1 :> 1 @@ 4 :> 3 @@ 9 :> 5)

BagCardinality(bag)
  The sum of all values in ``bag``.
  
  ::

    BagCardinality(EmptyBag) = 0
    BagCardinality([a |-> 2]) = 2
    BagCardinality([a |-> 5, b |-> 3, c |-> 1]) = 9

CopiesIn(e, bag)
  If ``e`` is in ``bag``, then ``bag[e]``, otherwise 0.
  
  ::

    CopiesIn("a", EmptyBag) = 0
    CopiesIn("a", [a |-> 5, b |-> 3]) = 5

.. _tlc_module:

TLC
============

Required for PlusCal `assert <assert>`. Many of the operators in TLC break core assumptions about TLA+, such as referential transparency. Use with caution!

``a :> b``
  The function ``[x \in {a} |-> b]``.

``func1 @@ func2``
  Function merge. If two functions share the same key, uses the value from ``func1`` (**NOT** ``func2``).


Permutations(set)
  The set of all functions that act as permutations of ``set``. eg

  ::

    >>> Permutations({"a", "b"})

    {[b |-> "b", a |-> "a"], 
     [b |-> "a", a |-> "b"]}
  
  

SortSeq(seq, Op(_, _))
  Sorts the sequence with comparator ``Op``.

ToString(val)
  String conversion.

JavaTime
  The current epoch time.

Print(val, out)
  Prints ``ToString(val)``, and evaluates to ``out`` as an expression.

PrintT(val)
  Equivalent to ``Print(val, TRUE)``.

Any
  ``x \in Any`` for *any* value ``x``. Don't use this as part of a ``Spec``, but it's occasionally useful for modeling properties.

Assert(bool, errmsg)
  If ``bool`` is false, then terminates model checking with ``errmsg``. Otherwise, evaluates to TRUE.

RandomElement(set)
  *Randomly* pulls an element from ``set``. The value can be different on different runs!

TLCEval(v)
  Evaluates the expression ``v`` and caches the result. Can be used to speed up recursive definitions.


.. _tlcget:

TLCGet(val)
  val can be either an integer or a string. If an integer, retrieves the value from the corresponding TLCSet. If a string, retrieves statistics from the current model run. The following strings are valid:

  - "queue"
  - "generated"
  - "distinct"
  - "duration": number of seconds elapsed since the beginning of model checking
  - "level": the length of the *current* behavior
  - "diameter": the length of the longest *global* behavior
  - "stats": all of the global stats (everything excluding "level"), as a struct.

  .. from https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/module/TLCGetSet.java

  ``TLCGet("level")`` can be used to :ref:`bound an unbound model <topic_unbound_models>`.

TLCSet(i, val)
  Sets the value for ``TLCGet(i)``. ``i`` must be a positive integer. TLCSet can be called multiple times in the same step.
  
  .. note:: Each TLC worker thread carries a distinct "cache" for the values of ``TLCGet(i)``. As such, it's generally inadvisable to use ``TLCSet`` to profile information that lasts beyond a single step.

    TLCSet statements evaluated during the initial state, however, *will* be propagated to all workers.

.. |noenumerate| replace:: Cannot be enumerated by TLC (used in a `quantifier <quantifier>` or a `CHOOSE`), but can be used for membership checking.
.. |fromdocs| replace:: [taken from docs]

TLCExt
------

.. todo:: Figure out PickSuccessor

AssertEq(a, b)
  Equivalent to ``a = b``, except that if ``a # b``, it also prints the values of ``a`` and ``b``. This *does not* terminate model checking!

AssertError(str, exp)
  True if ``exp`` doesn't throw an error, or if ``exp`` throws an error that *exactly* matches ``str``. False otherwise.

  .. note:: AssertError catches the thrown error, meaning model checking will continue.

Trace
  Returns the "history" of the current behavior, as a sequence of structs.

TLCModelValue(str)
  Creates a new model value with name ``str``. Can only be used in constant definitions, as part of an ordinary assignment.

  .. code:: none

    CONSTANT Threads <- {
      TLCModelValue(ToString(i)): i \in 1..3
    }

Json
====

ToJson(val)
  Converts ``val`` to a JSON string. Sets and sequences are encoded as arrays, functions are encoded as objects with string keys.

  .. code:: none

    >>> ToJson(1..3)
    "[1,2,3]"

    >>> ToJson([x \in 0..2 |-> x^2])

    "{\"0\":0,\"1\":1,\"2\":4}"

  Multi-arity functions are encoded with keys that use the TLA+ tuple notation.

  .. code:: none

    >>> ToJson([p, q \in BOOLEAN |-> p => q])
    
    "{\"<<FALSE, FALSE>>\":true,
      \"<<TRUE, FALSE>>\":false,
      \* ...

JsonSerialize(absoluteFilename, value)
  Exports ``value`` as a JSON object to a file. 

JsonDeserialize(absoluteFilename)
  Imports a JSON object from a file.


Randomization
=============

This module defines operators for choosing pseudo-random subsets of a set. If you use this, **TLC will not check all possible states.** For example, consider the spec

::

  EXTENDS Integers, TLC, Randomization
  VARIABLE x

  Init == 
      /\ x = 0

  Next ==
      \/ /\ x = 0
         /\ x' \in {1, 2, 3}
      \/ /\ PrintT(x)
         /\ UNCHANGED x

  \* Magic magic magic
  Spec == Init /\ [][Next]_x

Running this will print the numbers {0, 1, 2, 3}. If we replace ``{1, 2, 3}`` with ``RandomSubset(2, {1, 2, 3})``, then it will only print two of those three numbers, and *which two* may change from run to run. This makes ``Randomization`` useful for optimization, but you need to be careful.

RandomSubset(k, S)
  Returns a random size-k subset of S.

  ::

    RandomSubset(1, {"a"}) = {"a"}
    \* Running multiple times will yield different subsets
    RandomSubset(2, {"a", "b", "c"}) = {"b", "c"}
    RandomSubset(2, {"a", "b", "c"}) = {"a", "c"}

RandomSetOfSubsets(k, n, S)
  Selects k random subsets of S, where each random subset has *on average* n elements. Since this process may result in some duplicate subsets, the operator can potentially return fewer than k subsets. This can also potentially return the empty set.

  ::

    RandomSetOfSubsets(1, 1, {"a"}) = {{"a"}}

    \* Each element has a 3-in-5 chance of appearing in each subset
    RandomSetOfSubsets(2, 3, {"a", "b", "c", "d", "e"}) = {{"a", "d", "c"}, {"a", "b", "e", "c"}}
    RandomSetOfSubsets(2, 3, {"a", "b", "c", "d", "e"}) = {{"a", "e"}, {"d", "e", "b", "c"}}

    \* Fewer than 4 results because it generated a duplicate
    RandomSetOfSubsets(4, 1, {"a", "b"}) = {{}, {"b"}, {"a", "b"}}

TestRandomSetOfSubsets(k, n, S)
  Calls ``RandomSetOfSubsets(k, n, s)`` five times and returns the number of unique sets returned each time.

  ::

    TestRandomSetOfSubsets(1, 1, {"a"}) = <<1, 1, 1, 1, 1>>
    \* Different executions will yield different results:
    TestRandomSetOfSubsets(3, 4, {"a", "b", "c", "d", "e"}) = <<3, 3, 2, 2, 2>>


