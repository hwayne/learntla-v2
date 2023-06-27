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

Required for `pluscal procedures <procedure>`.

Seq(set)
  The set of all sequences where the values are all elements of ``set``. |noenumerate| 

Len(seq)
  Length of ``seq``.

Head(seq)
  First element of ``seq``.

Tail(seq)
  All but first element of ``seq``.

``seq1 \o seq2``
  Sequence concatination.

Append(seq, e)
  Equivalent to ``seq1 \o <<e>>``.
  
SubSeq(seq, m, n)
  The sequence ``<<s[m], s[m+1], ... , s[n]>>``. |fromdocs|

SelectSeq(seq, Op(_))
  Sequence filter.

FiniteSets
============

IsFiniteSet(set)
  Tests if ``set`` is not an infinite set.

Cardinality(set)
  The number of elements in ``set``.

Bags
============

Also known as multisets. Bags are functions items to "counts" of items. IE the struct ``[a |-> 1, b |-> 2]`` is a bag. The values of a bag must be positive integers.

IsABag(func)
  Tests if ``func`` is a bag.

BagToSet(bag)
  Equivalent to ``DOMAIN bag``.

SetToBag(set)
  Equivalent to ``[x \in set |-> 1]``.

BagIn(e, bag)
  Equivalent to ``e \in DOMAIN bag``.

EmptyBag
  Equivalent to ``<<>>``.

``bag1 (+) bag2``
  Bag addition. Creates a new bag where each key is the sum of the values of that key in each bag.

``bag1 (-) bag2``
  Bad subtraction. If ``bag2[e] >= bag1[e]``, then ``e`` is dropped from the final bag's keys.

  .. todo:: Topic of a bag that goes Nat instead of Nat-0

BagUnion(set)
  Equivalent to ``bag1 (+) bag2 (+) ...``, where ``set = {bag1, bag2, ...}``.

``B1 \sqsubseteq B2``
  B1 \sqsubseteq B2 iff, for all e, bag B2 has at least as many copies of e as bag B1 does. |fromdocs| 
  
SubBag(bag)
  The set of all subbags of ``bag``.

BagOfAll(Op(_), bag)
  If ``bag[e] = x``, then ``out[Op(e)] = x``. eg

  ::

    b == <<1, 3, 5>>
    >>> BagOfAll(LAMBDA x: x^2, b)

    (1 :> 1 @@ 4 :> 3 @@ 9 :> 5)

BagCardinality(bag)
  The sum of all values in ``bag``.

CopiesIn(e, bag)
  If ``e`` is in ``bag``, then ``bag[e]``, otherwise 0.


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

  .. todo:: Write about using TLCGet for bounding models

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

.. todo:: Explain randomization module when I understand the actual guarantees it gives

JsonSerialize(absoluteFilename, value)
  Exports ``value`` as a JSON object to a file. 

JsonDeserialize(absoluteFilename)
  Imports a JSON object from a file.
