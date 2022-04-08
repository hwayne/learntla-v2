.. _chapter_tla:

########
TLA+
########

PlusCal is a formalism designed to make using formal methods easier. By learning pluscal first, we can focus on teaching first logic and model checking, leaving temporal logic for later. But we also have the 

Another advantage of learning PLusCal first: we can bootstrap TLA+ from it by looking at what the pluscal generates, and infer the tla+. We know that the pluscal generated is valid TLA+, so we can use it to understand the TLA+.

Concepts
============

TLA+ is a third-generation formal method, based on issues seen with LTL and Z. In that regard, it makes two core requirements:

1. all sepcs are stutter-invariant
2. All variables must always be assigned.

.. index:: Action

We saw in the `last chapter <chapter_action_properties>` all the base components that drive a TLA+ spec:

* The prime operator: ``x'`` is the value of x *in the next state*.
* The box operator: ``[P]_x`` is ``P \/ UNCHANGED x``.


I find the easiest way to explain what's going on with TLA+ is to relate it to what the PlusCal does. In his original book `Specifying Systems`_, Leslie Lamport introduces TLA+ with a specification of an hour clock, and I'd be remiss to break with tradition. The pluscal is a *mostly* faithful translation of his TLA+ spec.

.. hc

You should be able to look at this spec and run it in your head, know exactly what it does. ``hr`` starts at some value between 1 and 12, and then it increments, rapping at 12 back to 1. The TLA+ translation *must* be doing the same thing. Let's take a look at it:

.. trnaslation

There are operators: ``Init``, ``Next``, and ``Spec``. ``Spec`` is what we always put as "the temporal property to run", so that's the core of the TLA+ specification.

In ``Next``, we've replaced ``hr := 1`` with ``hr' = 1``. As we learned in the `last chapter <_chapter_action_properties>`, ``hr'`` is the value of ``hr`` in the *next* state. ``hr' = 1`` is a *boolean* statement, which is true or false. In fact, ``Next`` is a boolean operator: it's either true or false. It is true if it accurately describes the value of ``hr`` in the next state, and false if it doesn't.

.. todo:: explain this better?

.. index:: action

An boolean operator that contains primed variables is called an **action**. It's the titular action in *Temporal Logic of Action* (plus).

.. todo:: note on the name TLA+

``Next`` is used in ``Spec``, as part of ``[][Next]_vars``. Recall `the definition of []_x <box_action>`. Expanding the definition:

::

  Spec == Init /\ [](Next \/ UNCHANGED vars)

By convention, in a temporal formula, anything outside a temporal operator (``[]`` or ``<>``) is tested as true in the initial state. So ``Spec`` says:

* In the initial state, ``Init`` is true, and
* It is always true that ``Next \/ UNCHANGED vars`` is true.

Since ``Next`` is an action, to be "always true" it must always accurately describe the new values of the system.

PLAN:

  * UNCHANGED in actions
  * A with (``x' \in Set``)
  * An either (nondeterminisim)
  * await
    * Leads to nonaction booleans
  * processes
  * fucntions except
  * Fairness
    * Strong fairness

A TLA+ Spec From Scratch
=========================



What you can do with TLA+:

  * Multiple actions simutaneously
  * Or
  * Strong fairness on branches
  * Refinement (next chapter)
TODO

.. _Specifying Systems: https://lamport.azurewebsites.net/tla/book-02-08-08.pdf
