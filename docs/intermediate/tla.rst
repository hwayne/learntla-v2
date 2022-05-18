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

Learning from PlusCal
======================

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

.. note::

  Technically speaking, we can use TLA+ to describe **any possible set of behaviors**. This is technically a valid spec:

  ::

    Init == x = 0
    Next == x' >= x
    Spec == Init /\ [][Next]_x

  This is a valid tla+ spec, and the behavior 1 → 9 → 17 → 17.1 → 84 is a valid behavior of this spec. It's just not a spec that TLC can generate. It's a tool made by mortal men.


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

In typical TLA+ usage, we'd instead write ``UNCHANGED x``. In fact there's some syntactic sugar here, we can write ``UNCHANGED <<x, y, z>>`` to mean "none of x, y, or z change".

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
                       hr' = hr + x


This is more interesting! {{We "assign" ``hr' `` inside the quantifier.}}

That should tell us the following is also ok:

::

  Next == IF hr = 12
             THEN /\ hr' = 1
             ELSE \/ hr' = hr + 1
                  \/ hr' = hr + 2

And that's in fact how ``either`` is translated.

EXCEPT
---------

Before we go onto concurrency, there's one thing I want to get out of the way first. What's wrong with the following spec?

.. code-block::

  VARIABLE s

  Init == s = <<TRUE, FALSE>>

  Next == s[1]' = FALSE

  Spec == Init /\ [][Next]_s

(I mean, besides the missing module name.)

If you run it, you will get this *very helpful error*:

| In evaluation, the identifier s is either undefined or not an operator.

But s *is* defined, it's a variable right there!

The problem is actually a subtle nuance of assigning to functions. In ``Next``, we're only giving the next state of ``s[1]``. Here are some values of ``s'`` that would satisfy ``Next``:

#. ``<<FALSE, FALSE>>``
#. ``<<FALSE, TRUE>>``
#. ``<<FALSE, 186>>``
#. ``<<FALSE>>``
#. ``0 :> 🌽 @@ 1 :> FALSE @@ 19 :> 🌽🌽🌽``

Remember, TLA+ wants you to be as precise as possible. If you didn't specify that ``s[2]'`` is the same as ``s[2]``, it doesn't have to be. TLC naturally considers this an error.

What we actually wanted to write is that ``s'`` is the same as ``s`` *except* that ``s[1]`` is false. Here's the syntax for that:

.. code-block::

  Next == s' = [s EXCEPT ![1] = FALSE]

Yes, I know it's really awkward. No, I don't know of anything better. ``EXCEPT`` has a couple bits of syntactic sugar to make using it a wee bit more pleasant. First of all, we can assign multiple keys in the same statement:

.. code-block::

  Next == s' = [s EXCEPT ![1] = FALSE, ![2] = 17]

Second, we can reference the original value of the key with ``@``.

.. code-block::

  IncCounter(c) == 
    counter' = [counter EXCEPT ![c] = @ + 1]

Finally, we can {{do nested lookups in the ``EXCEPT``}}:

.. code-block::

  Init == s = <<[x |-> TRUE], FALSE>>

  Next == s' = [s EXCEPT ![1].x = ~@]

{{PlusCal will naturally convert function assignments to ``EXCEPT`` statements.}}

pc
-----



PLAN:

  * await
    * Leads to nonaction booleans
  * processes
  * fucntions except
  * Fairness
    * Strong fairness

Weak Fairness
-------------

A TLA+ Spec From Scratch
=========================

Strong Fairness
---------------

For this spec, we have a worker doing some abstract job. It can succeed or fail. If it fails, it retries until it succeeds. We make both ``Succeed`` and ``Retry`` weakly fair and leave ``Fail`` unfair. 

::

  VARIABLES status

  Init == status = "start"

  ChangeStatus(from, to) == status = from /\ status' = to

  Succeed == ChangeStatus("start", "done")
  Fail == ChangeStatus("start", "fail")
  Retry == ChangeStatus("fail", "start")

  Next == Succeed \/ Fail \/ Retry \/ UNCHANGED status

  Fairness ==
    /\ WF_status(Succeed)
    /\ WF_status(Retry)

  Spec == Init /\ [][Next]_status /\ Fairness

  Liveness == <>(status = "done")

  ====

Does ``Liveness`` hold? It does not! Our fairness clause only says that if ``Succeed`` is guaranteed if it is *permanently* enabled. The problem it's *not* permanently enabled. We could have the following error trace:

.. code-block::
  <Init>    status = "start"

  <Fail>*   status = "fail"

  <Retry>   status = "start"
  <Fail>*   status = "fail"
  <Retry>   status = "start"
  ...

After every step marked ``*``, ``status /= "start"``, so ``Succeed`` is not enabled. ``Retry`` _is_ enabled, and no action at this point can disable it, so it's guaranteed to happen. Now we're back with ``status = "start"``, and ``Succeed`` is enabled again. But then ``Fail`` happens and changes ``status``...

Since ``Succeed`` keeps flipping between enabled and disabled, weak fairness can't guarantee it happens. If we want to make sure ``Succeed`` happens we need to make it **strongly fair**. Strong fairness says that if an action isn't permanently disabled it will eventually happen. Unlike weak fairness the action can be _intermittently_ enabled and is still guaranteed to happen. 

.. code-block:: diff

  Fairness ==
  + /\ SF_status(Succeed)
  - /\ WF_status(Succeed)
    /\ WF_status(Retry)

This satisfies ``Liveness``.


What you can do with TLA+:

  * Multiple actions simutaneously
  * Or
  * Strong fairness on branches
  * Refinement (next chapter)
  * Refactoring actions
TODO

.. _Specifying Systems: https://lamport.azurewebsites.net/tla/book-02-08-08.pdf
.. [#plus] The "plus" is for the addition of ZF set theory.
