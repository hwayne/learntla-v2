.. _topic_unbound_models:

+++++++++++++++++++++++
Handling Unbound Models
+++++++++++++++++++++++

Do not run this spec:

::

  ---- MODULE Unbound ----
  EXTENDS Integers

  (*--algorithm seriously_dont_run_this
  variable x = 0
  begin
    while TRUE do
      x := x + 1;
    end while;
  end algorithm; *)
  
.. index::
  single: Model; unbound models
  single: unbound models

The model checker works by finding all possible distinct states. In this spec, there are an infinite number of distinct states; x can keep increasing forever. So this will never finish model checking. This is called an :dfn:`unbound model`.

Unbound models generally come from one of two places:

1. The spec keeps incrementing an integer value, as seen above
2. The spec keeps appending to a sequence.

Be aware that it's not just top-level values that can be unbound. If you have a structure :ref:`of type <struct_set>` ``[a: Int, b: BOOL]``, then such a struct can be unbound on the ``a`` key.

.. tip:: 

  A good way to sense if a model is unbound: is it generating *way* more states than you expected it to? Is the diameter increasing much faster than you expected? Most bound models increase in diameter slowly, while unbound models find a chain of new states quickly.


.. index::
  single: Invariant; Model Invariants

.. _model_invariant:

Model Invariants
================

The easiest way to detect an unbound model is to add a ``ModelInvariant`` to your spec. The model invariant is like the type invariant, except it restricts every variable to a finite set. 

::

  CONSTANT MaxX

  TypeInvariant == x \in Int
  ModelInvariant == x \in 0..MaxX

Notice that ``ModelInvariant => TypeInvariant``: a state that breaks the model invariant *could* be well-typed, but a type error is also a model error. Also, ``ModelInvariant => Bound``. A bound model could spuriously fail the model invariant, but an unbound model will *definitely* fail.

Bounding Models
================

*Most* of the time, an unbound model is a spec error: you left a check off somewhere and the model checker exploited that. Fixing the bug or modifying the spec is usually enough to rebound the model.

.. todo:: Example of a spec that can't easily be rebound

But sometimes you can't easily do this without adding new assumptions into the spec. In these cases, you can add a :ref:`state constraint <state_constraint>`.

::

  ModelConstraint == x \in 0..MaxInt

This is identical to the model invariant, with one crucial difference: by using it as an invariant, the model checker will *reject* violating states instead of raising them as an error. The spec still has an infinite state space, but the model checker will only explore a finite part of it. This makes the model bound.

.. warning:: Don't do this if you're also checking :ref:`temporal properties <chapter_temporal_logic>`! You're effectively "cutting off" part of the behavior, so model checker doesn't have the whole behavior to evaluate liveness with.

TLCGet
-------

The :ref:`TLC module <tlc_module>` has the special operator `TLCGet <tlcget>`. This has a few different uses, but the main one for us is that we can get runtime statistics, like the number of states generated and the length of the current trace. This is also my favorite way to limit the state space of an unbound model:

::

  ModelConstraint == TLCGet("level") < 9

What makes this better than constraining the values of the variables? If you have a lot of different variables, it can be tough to predict what the bounds for each should be. It's a lot easier, at least to start, with saying they're all unbounded, but limit how many steps the model checker can take.
