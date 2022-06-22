.. _topic_state_machines:

#######################
State Machines
#######################

The dirty secret of formal methods is that the only way we know to scale it up is to use state machines. So we might as well learn how to write state machines in TLA+!

Basic State Machines
====================

.. note:: Right now this is all very abstract, I'll make a better example later

`Here's <http://howtomakeanrpg.com/a/state-machines.html>`__ a good introduction to state machines. Let's start by modeling the state machine in that article:

.. todo:: https://www.smashingmagazine.com/2018/01/rise-state-machines/
.. graphviz:: 

  digraph StateMachine {
    A -> B -> C -> A;
    B -> A;
  }

Need to be nondeterministic

In PlusCal, we'd model a state machine by placing `await` statements inside an `either` block. If the ``await`` is false the branch is blocked off, but the other branches are still available, preserving nondeterminism.

...

(We could of course nest the ``fetching`` nondeterministic branch into another nested either statement, which would save us one extra ``await``.)


In TLA+, we can use the same trick the PlusCal translator uses to model sequential processes.



...


Hierarchical State Machines
=============================

What's better than a state machine? A *nested* state machine.

Also known as `Harel Statecharts <https://www.cs.scranton.edu/~mccloske/courses/se507/harel_Statecharts.pdf>`__, hierarchical state machines allow transitions inside

.. digraph:: hsl

  compound=true;

  subgraph cluster_A {
    label=A;
    B;
    C;
  }
  D -> C;
  B -> D[ltail="cluster_A"];
