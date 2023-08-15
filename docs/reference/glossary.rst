++++++++++++++++
Glossary
++++++++++++++++

Term Guide
==========

.. glossary::
  :sorted:

  Action
    A predicate that describes how a state "evolves". Any boolean expression with a primed operator (like ``x' = x``). Actions are true if they describe the next state and false if they don't. Multiple actions can be true at once, for example if two things happen in parallel.

  Behavior
    A sequence of states, or "timeline", in the system.

  Enabled
    An action is "enabled" if it can "happen" this step, ie potentially describe the next step.

  Fairness
    A guarantee that a system will eventually "make progress". Weak fairness says that if the given action is *permanently enabled*, it will eventually happen. Strong fairness says that if the action is not *permanently disabled*, it will eventually happen.

  Formal Methods
    The discipline of writing rigorous, verified code.

  Formal Specification Language
    A language you use to describe a system you're building, so you can find errors in it.

  Function
    A mathematical function, with a fixed domain. Programming functions are called operators.

  Liveness
    A property that a good thing *is guaranteed* to happen. All liveness properties are temporal properties.

  Invariant
    Something that must be true at every state in the system. All invariants are safety properties.

  Model
    In TLA+, a specification + a set of injected parameters and required invariants.

  Model checking
    The most common way of verifying a specification matches its properties: generate every possible behavior and exhaustively test if any of them break your properties. The model checker for TLA+ is called TLC.

  Operator
    The TLA+ equivalent of a programming function. Operators with primed variables in them are called actions.

  PlusCal
    A DSL for writing TLA+ algorithms.

  Property
    Something we want to be true of the system. All properties in TLA+ can be broken into safety and liveness properties.

  Predicate
    A boolean expression.

  Safety
    A property that a bad thing *doesn't* happen. Most (but not all) safety properties are invariants. All invariants are safety properties.

  Specification
  Spec
    A rigorous mathematical description of the system you're building.

  State space
    The set of all possible states reachable by all possible behaviors in a model.

  Step
    A single "tick" of the clock, changing some of the spec's state. A behavior is composed of a sequence of steps.

  Stutter Step
    A state transition that doesn't change anything. All TLA+ specs are "stutter-invariant", meaning they can always stutter between any two "real" actions. A behavior can stutter forever unless otherwise prevented by a fairness constraint.

  Temporal Property
    A property that spans more than one state. For example, "the counter must never decrease" or 

  Theorem Prover
    An alternate way to formally verify specifications, where you mathematically prove it has the properties you want. Much more difficult than model checker and so this guide doesn't cover it. The theorem prover for TLA+ is called `TLAPS <https://tla.msr-inria.inria.fr/tlaps/content/Home.html>`__.

  TLA+
    The "Temporal Logic of Actions", used for modeling concurrent systems. A :term:`formal specification language`. You can either write in TLA+ directly or use the :term:`PlusCal` DSL.

  TLA+ Toolbox
    The official TLA+ IDE.

  TLC
    The name of the model checker for TLA+. The site uses "TLC" and "model checker" interchangeably.



..

  State space explosion
  Quantifier
  Module
  Machine
  World
