++++++++++++++++
Glossary
++++++++++++++++

`genindex`

Term Guide
==========

.. glossary::
  :sorted:

  TLC : Tooling
    The name of the model checker for TLA+. The site uses "TLC" and "model checker" interchangeably.

  PlusCal
    A DSL for writing TLA+ algorithms.

  TLA+
    The "Temporal Logic of Actions", used for modeling concurrent systems. A :term:`formal specification language`. You can either write in TLA+ directly or use the :term:`PlusCal` DSL.


  Formal Specification Language
    A language you use to describe a system you're building, so you can find errors in it.

  Formal Methods
    The discipline of writing rigorous, verified code.

  Safety
    A property that a bad thing *doesn't* happen. Most (but not all) safety properties are invariants. All invariants are safety properties.

  Liveness
    A property that a good thing *is guaranteed* to happen. All liveness properties are temporal properties.

  Invariant
    Something that must be true at every state in the system. All invariants are safety properties.

  Property
    Something we want to be true of the system. All properties in TLA+ can be broken into safety and liveness properties.

  Temporal Property
    A property that spans more than one state. For example, "the counter must never decrease" or 

  Predicate
    A boolean expression.

  Behavior
    A sequence of states, or "timeline", in the system.

  State space
    The set of all possible states reachable by all possible behaviors in a model.

  TLA+ Toolbox
    The official TLA+ IDE.

..

  State space explosion
  Quantifier
  Model
  Spec
  Module
  Model Checking
  Machine
  World

Symbol Guide
============

@@ : Symbol
  Test
