.. _topic_toolbox:

###########################
Using the Toolbox
###########################

Error Traces
==============

Error Trace Information
------------------------

Trace Explorer
------------------------

How it works
Allows primes

Model Configuration
========================

This is **not** comprehensive. Only showing what's important

Additional Spec Options
-----------------------

State Constraint

  TLC will ignore any states of the model that don't satisfy the state constraint. For example, if your constraint is ``x < 5``, states where ``x = 5`` will be discarded and no new states will be found from them.

  Invariants **will** be checked first, though, before the state is discard. The model-checking may fail even if the state is one that should have been ignored. The state constraint only prevents TLC from searching from new states *from* the discarded state.

  Liveness invariants can't be checked when the state constraint is active.

Action Constraint

  Similar to a state constraint, except it's an action. You can eg write ``x' = x`` to only explore the subset of the state space where ``x`` remains the same as its initial value.



Additional TLC Options
-----------------------

Worker threads

  How many workers to distribute TLC checking across. By default, this is the number of cores. Using fewer threads will (generally) make TLC take longer and use fewer CPU resources. Using one thread will guarantee a deterministic model checking across runs, which may be useful if you're using print statements.

.. todo:: remote checking

Fraction of memory:
  For small specs, takes time to allocate memory

  View

    This one's dark magic and should be treated *very* carefully. Normally TLA+ distinguishes states by using all variables. If you define a ``VIEW`` expression, then that becomes the criteria TLC uses instead.

    For example, let's say you have two variables, x and y. The default VIEW would be ``<<x, y>>``. If you instead wrote ``VIEW x``, any two states with the same x will be treated as the same state, *regardless of the value of y*. 

    Used wisely, this can be useful in optimizing models. Used poorly, it can completely wreck your spec.

    .. todo:: I think it is actually more complicated, it's only how TLC knows when to *stop* checking

  Depth-first
    Normally TLC does a breadth-first search. This switches it to instead do a depth-first search. This is useful if you expect an invariant violation to be common-but-deep in the behavior. It's also a good way to check parts of unbound models, as you can specify a maximum depth to check.

  Simulation Mode
    Random, doesn't stop, doesn't check liveness properties Maximum Length of trace

    Simulation mode runs never stop, even if they've exhaustively checked the state space. You have to end them manually.

  Visualize state graph
    Requires `graphviz`_. Generates a directed graph after the end of model checking. This can be useful for understanding small state spaces. But for large state spaces you're better off `dumping <dump>` the output yourself and pruning the graph or loading it into something like `Gephi`_.

TLC command-line parameters


Profiler
=============

Misc Features
================

.. _graphviz: tasdasda

.. _Gephi: https://gephi.org/
