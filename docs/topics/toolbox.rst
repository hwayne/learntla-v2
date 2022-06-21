.. _topic_toolbox:

###########################
Using the Toolbox
###########################

The toolbox has a number of power-user tools to make using it easier.

Error Traces
==============

Let's create a simple spec to look at how the error trace works.

Error Trace Information
------------------------


Trace Explorer
------------------------

How it works
Allows primes

Model Configuration
========================

This is **not** comprehensive. More comprehensive notes can be found in the toolbox help files and TK.

Additional Spec Options
-----------------------

State Constraint

  TLC will ignore any states of the model that don't satisfy the state constraint. For example, take this spec:
  
  .. todo:: add the numbers

  ::

    EXTENDS Integers
    VARIABLE x

    Init == x = 0
    Next == x' = x + 1
    Inv == x < 10
    Spec == Init /\ [][Next]_x

  Normally, running this with ``INVARIANT Inv`` will make this fail. But if you add the state constraint ``x < 5``, then it passes with six states found. States where ``x >= 5`` will be discarded and no new states will be found from them.

  Invariants **will** be checked first, though, before the state is discarded. This means that if we change the state constraint to ``x < 10``, it will fail. The state constraint only prevents TLC from searching from new states *from* the discarded state.

  A good use for state constraints is to bound unbound specifications.

  Liveness invariants can't be checked when the state constraint is active.

Action Constraint

  Similar to a state constraint, except it's an action. In the above spec, you can write ``x' > x`` to only explore states where x increases.



Additional TLC Options
-----------------------

.. todo:: {CONTENT} remote checking

Worker threads

  How many workers to distribute TLC checking across. By default, this is the number of cores. Using fewer threads will (generally) make TLC take longer and use fewer CPU resources. Using one thread will guarantee a deterministic model checking across runs, which may be useful if you're using print statements.


Fraction of memory
  How much memory TLC can use for checking. If the model exceeds this limit then TLC will start writing found states to disk, significantly increasing model-checking time.

  Note that TLC needs to preallocate all of the memory before it starts model checking, and then free it afterwards. For small enough models and large enough computers, allocation time can exceed the model runtime! 

View

  This one's dark magic and should be treated *very* carefully. Normally TLA+ distinguishes states by using all variables. If you define a ``VIEW`` expression, then that becomes the criteria TLC uses instead.

  For example, let's say you have two variables, x and y. The default VIEW would be ``<<x, y>>``. If you instead wrote ``VIEW x``, any two states with the same x will be treated as the same state, *regardless of the value of y*. 

  Used wisely, this can be useful in optimizing models. Used poorly, it can completely wreck your spec. 

Depth-first
  Normally TLC does a breadth-first search. This switches it to instead do a depth-first search. This is useful if you expect an invariant violation to be common-but-deep in the behavior. It's also a good way to check parts of unbound models, as you can specify a maximum depth to check.

Simulation Mode
  In this mode, TLC will generate random traces up to the maximum length of trace. It will not check liveness.

  Simulation mode runs never stop, even if they've exhaustively checked the state space. You have to end them manually.

Visualize state graph
  Requires `graphviz`_. Generates a directed graph after the end of model checking. This can be useful for understanding small state spaces. But for large state spaces you're better off `dumping <dump>` the output yourself and pruning the graph or loading it into something like `Gephi`_.

TLC command-line parameters
  You can pass additional command line parameters to TLC that aren't exposed in the toolbox GUI. See `here <tlc_options>` for more information on what you can pass in.



Profiler
=============

.. _toolbox_misc:

Misc Features
================

- There's autocomplete with ``ctrl+space``.
- Pressing ``F3`` on a module name will jump to its definition.  
.. _graphviz: https://graphviz.org/

.. _Gephi: https://gephi.org/
