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

.. note:: The spec doesn't *yet* reference the ``A`` label. We'll see how it plays in later.

There are operators: ``Init``, ``Next``, and ``Spec``. ``Spec`` is what we always put as "the temporal property to run", so that's the core of the TLA+ specification.

In ``Next``, we've replaced ``hr := 0`` with ``hr' = 1``. As we learned in the `last chapter <chapter_action_properties>`, ``hr'`` is the value of ``hr`` in the *next* state. ``hr' = 1`` is a *boolean* statement, which is true or false. In fact, ``Next`` is a boolean operator: it's either true or false. It is true if it accurately describes the value of ``hr`` in the next state, and false if it doesn't.

.. todo:: explain this better?

.. index:: action

A boolean operator that contains primed variables is called an **action**. It's the titular action in *Temporal Logic of Actions* (plus). [#plus]_

``Next`` is used in ``Spec``, as part of ``[][Next]_vars``. Recall `the definition of []_x <box_action>`. Expanding the definition:

::

  Spec == Init /\ [](Next \/ UNCHANGED vars)

By convention, in a temporal formula, anything outside a temporal operator (``[]`` or ``<>``) is tested as true in the initial state. So ``Spec`` is true iff:

* In the initial state, ``Init`` is true, and
* ``Next \/ UNCHANGED vars`` is always true in every step.

Since ``Next`` is an action, to be "always true" it must always accurately describe the new values of the system. Formally, we call it the dfn:`Next State Relationship`. This gives us the blueprint for what spec is.

UNCHANGED
---------

Before we add more elaborate logic, let's make a small noop change:

.. spec

Notice we're not *using* x, just defining it. Nothing about the output should change except the initialization, right?

::

  Next == /\ IF hr = 12
                THEN /\ hr' = 1
                ELSE /\ hr' = hr + 1
          /\ x' = x

Despite x not appearing anywhere, the translator added the ``x' = x`` line. This is because of a *foundational* rule of TLA+ specs: **The next action must fully describe all variables**. If you remove that line and run the spec (without retranslating), you'll get something like this:

| Error: Successor state is not completely specified by the next-state action. The following variable is not assigned: x.

In typical TLA+ usage, we'd instead write ``UNCHANGED x``. In fact there's some syntactic sugar here, we can write ``UNCHANGED <<x, y, z>>`` to mean ``x' = x /\ y' = y /\ z' = z``.

with
-----

First, let's see what happens when we do a deterministic with:

.. spec

::

  Next == IF hr = 12
             THEN /\ hr' = 1
             ELSE /\ LET x == 1 IN
                       hr' = hr + 1



Okay, that's done through a `LET`, which makes sense. It's a 1-1 translation. It also explains why you can't put labels inside a ``with`` statement, since ``LET`` is just a temporary binding. 

Now for nondeterministic with:

.. spec

::

  Next == IF hr = 12
             THEN /\ hr' = 1
             ELSE /\ \E x \in 1..2:
                       hr' = hr + 1


This is more interesting!

either
--------

pc
-----



PLAN:

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
  * Refactoring actions
TODO

.. _Specifying Systems: https://lamport.azurewebsites.net/tla/book-02-08-08.pdf
.. [#plus] The "plus" is for the addition of ZF set theory.
