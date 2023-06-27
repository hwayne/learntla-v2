.. _example_partitions:

##########
Partitions
##########

Recently I got someone asking about a "pluscal puzzle":

.. rst-class:: quote
..

  I need an operator to generate all partitions of a set S. S is a constant/model variable.

  Each Partition is a set of Parts (and each Part is a set), such that::

    /\ Part \in SUBSET S
    /\ \A part1, part2 \in Partition: 
      part1 # part2 => part1 \intersect part2 = {}
    /\ UNION Partition = S


In other words:

.. rst-class:: quote
..

  ::

    Partitions(3) = 
    {
      { {1,2,3} },      
      { {1,2}, {3} },   
      { {1,3}, {2} },   
      { {1}, {2,3} },   
      { {1}, {2}, {3} } 
    } 

Let's implement this operator. To make things more general, I'm going to instead say that ``Partitions`` takes a set of values instead of a number.

The Operator
============

First, let's imagine for a second that instead of the elements being *sets* of sets, they were *sequences* of sets. So instead of ``{ {a,c}, {b} }``, the element was ``<< {a, c}, {b} >>``. Now notice that we can encode the same information as ``a :> 1 @@ b :> 2 @@ c :> 1``: "a" is in the first set, "b" is in the second set, etc.

And that's just a function in the function set ``[{a, b, c} -> 1..3]``! Every function in that set can be read as a mapping between values and the set in the partition they belong to. We just need an operator to go the *other* way, and convert "map of values to indices" to "indices to set of values".

::

  EXTENDS Integers, TLC, Sequences, FiniteSets
   
  PartitionsV1(set) == 
    LET F == [set -> 1..Cardinality(set)]
      G(f) == [i \in 1..Cardinality(set) |-> {x \in set: f[x] = i}]
    IN
      {G(f): f \in F}

  >> PartitionsV1({"a", "b"})
  {<<{}, {"a", "b"}>>, <<{"a"}, {"b"}>>, <<{"b"}, {"a"}>>, <<{"a", "b"}, {}>>}

Now it's just a matter of converting it back to sets. We can do this with a :ref:`set map <map>` and a ``Range`` helper. Note that ``Range`` to ``<<{1, 2}, {}>>`` gives us the set ``{{1, 2}, {}}``, which is why we have to set diff out the empty set.


::

  Range(f) == {f[x] : x \in DOMAIN f}

  Partitions(set) ==
      {Range(P) \ {{}}: P \in PartitionsV1(set)}
    
Performance Notes
=================

This operator is pretty inefficient, as a lot of the partitions are redundant: ``<<{1, 2}, {}>>`` is the same partition as ``<<{}, {1, 2}>>``. ``[1..n -> 1..n]`` has ``n^n`` elements, [#tetration]_ so the function set for ``1..4`` has 256 elements, while there are only 15 possible partitions. That's an overhead of over 10x!

In this case, though, I don't think the overhead matters too much. The main reason you'd want to generate a set of partitions is to use them as different configurations in your spec, in which case the cost of computing a 256-element set will be washed out by the cost of 15xing your state space.

(The number of partitions of a set follow the `bell numbers <https://en.wikipedia.org/wiki/Bell_number>`__.) 

.. [#tetration] Sometimes ``n^n`` is referred to as "tetration" and written as ²n. In this notation, ³n is ``n^(n^n)``. 
