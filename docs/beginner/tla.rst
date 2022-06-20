.. _chapter_tla:

########
TLA+
########

.. todo:: Fix the Pygments TLA+ parser
.. highlight:: none

PlusCal is a formalism designed to make using formal methods easier. By learning pluscal first, we can focus on teaching first logic and model checking, leaving temporal logic for later. Another advantage is that can bootstrap TLA+ from it by looking at what the pluscal generates, and infer the tla+. We know that the pluscal generated is valid TLA+, so we can use it to understand the TLA+.

.. index:: action

There are two concepts in the :doc:`last chapter <action-properties>` that you should review in order to understand TLA+:

* The prime operator: ``x'`` is the value of x *in the next state*.
* The box operator: ``[P]_x`` is ``P \/ UNCHANGED x``.

Now let's learn us some TLA+!

Learning from PlusCal
======================

I find the easiest way to explain what's going on with TLA+ is to relate it to what the PlusCal does. In his original book `Specifying Systems`_, Leslie Lamport introduces TLA+ with a specification of an hour clock, and I'd be remiss to break with tradition. The pluscal is a *mostly* faithful translation of his TLA+ spec.

.. spec:: tla/hourclock_1/hourclock.tla
  :ss: hourclock_1

You should be able to look at this spec and run it in your head. ``hr`` starts at some value between 1 and 12, and then increment, wrapping at 12 back to 1. The TLA+ translation *must* do the same thing. Let's take a look at it:

.. code:: none

  VARIABLE hr

  vars == << hr >>

  Init == (* Global variables *)
          /\ hr = 1

  Next == IF hr = 12
             THEN /\ hr' = 1
             ELSE /\ hr' = hr + 1

  Spec == Init /\ [][Next]_vars

.. note:: The spec doesn't *yet* reference the ``A`` label. We'll see how it plays in later.

First, we need to define the ``VARIABLES``, same way we define ``CONSTANTS``. Then there are operators: ``Init``, ``Next``, and ``Spec``. ``Spec`` is what we always put as "the temporal property to run", so that's the core of the TLA+ specification.

In ``Next``, we've replaced ``hr := 0`` with ``hr' = 1``. As we learned in the :doc:`last chapter <action-properties>`, ``hr'`` is the value of ``hr`` in the *next* state. ``hr' = 1`` is a *boolean* statement, which is true or false. In fact, ``Next`` is a boolean operator: it's either true or false. It is true if it accurately describes the value of ``hr`` in the next state, and false if it does not.

So for these choices of ``<<hr, hr'>>``, ``Next`` is *true*:

.. code:: text

  <<1, 2>>
  <<3, 4>>
  <<12, 1>>

And for these choices of ``<<hr, hr'>>``, ``Next`` is *false*:

.. code:: text

  <<1, 1>>
  <<12, 13>>
  <<4, 6>>
  <<9, "corn">>

.. note::

  And this gets to why = vs ``:=`` distinction in PlusCal is so weird, why we use ``=`` for initial variable assignment and equivalence checking and ``:=`` for updating. In TLA+, *it's all comparison*. ``x = 5`` is true if x is 5 in *this* state. ``x' = 5`` is true if x is five in *the next* state.

.. index:: action

A boolean operator that contains primed variables is called an **action**. It's the titular action in *Temporal Logic of Actions* (plus). [#plus]_

``Next`` is used in ``Spec``, as part of ``[][Next]_vars``. Recall `the definition of []_x <box_action>`. Expanding the definition:

.. code:: none

  Spec == Init /\ [](Next \/ UNCHANGED vars)

By convention, in a temporal formula, anything outside a temporal operator (`[] <always>` or `<> <eventually>`) is tested as true in the initial state. So ``Spec`` is true iff:

* In the initial state, ``Init`` is true, and
* ``Next \/ UNCHANGED vars`` is always true in every step.

Since ``Next`` is an action, to be "always true" it must always accurately describe the new values of the system. Formally, we call it the :dfn:`Next State Relationship`. This gives us the blueprint for what spec is.

.. note::

  Technically speaking, we can use TLA+ to describe **any possible set of behaviors**. This is technically a valid spec:

  .. code-block:: none

    Init == x = 0
    Next == x' >= x
    Spec == Init /\ [][Next]_x

  This is a valid tla+ spec, and the behavior 1 → 9 → 17 → 17.1 → 84 is a valid behavior of this spec. It's just not a spec that TLC can generate. It's a tool made by mortal men.


.. index:: UNCHANGED
.. _UNCHANGED:

Everything must be defined
--------------------------

Before we add more elaborate logic, let's make a small noop change:

.. spec:: tla/hourclock_2/hourclock.tla
  :diff: tla/hourclock_1/hourclock.tla

Notice we're not *using* x, just defining it. Nothing about the output should change except the initialization, right?

.. code:: none

  Next == /\ IF hr = 12
                THEN /\ hr' = 1
                ELSE /\ hr' = hr + 1
          /\ x' = x

Despite x not appearing anywhere, the translator added the ``x' = x`` line. This is because of a *foundational* rule of TLA+ specs: **The next action must fully describe all variables**. If you remove that line and run the spec (without retranslating), you'll get something like this:

  Error: Successor state is not completely specified by the next-state action. The following variable is not assigned: x.

In typical TLA+ usage, we'd instead write ``UNCHANGED x``. We can also write ``UNCHANGED <<x, y, z>>`` to mean "none of x, y, or z change".

with
-----

First, let's see what happens when we do a deterministic with:

.. spec:: tla/hourclock_3/hourclock.tla
  :diff: tla/hourclock_2/hourclock.tla

.. code:: none

  Next == IF hr = 12
             THEN /\ hr' = 1
             ELSE /\ LET x == 1 IN
                       hr' = hr + 1



Okay, that's done through a `LET`, which makes sense. It's a 1-1 translation. It also explains why you can't put labels inside a ``with`` statement, since ``LET`` is just a temporary binding. 

Now for nondeterministic with:

.. spec:: tla/hourclock_4/hourclock.tla
  :diff: tla/hourclock_3/hourclock.tla

.. code:: none

  Next == IF hr = 12
             THEN /\ hr' = 1
             ELSE /\ \E x \in 1..2:
                       hr' = hr + x

This is more interesting! We "assign" ``hr'`` inside the quantifier.

That should tell us the following is also ok:

.. code:: none

  Next == IF hr = 12
             THEN /\ hr' = 1
             ELSE \/ hr' = hr + 1
                  \/ hr' = hr + 2

And that's in fact how ``either`` is translated.

EXCEPT
---------

Before we go onto concurrency, there's one thing I want to get out of the way first. What's wrong with the following spec?

.. code-block:: none

  VARIABLE s

  Init == s = <<TRUE, FALSE>>

  Next == s[1]' = FALSE

  Spec == Init /\ [][Next]_s

(I mean, besides the missing module name.)

If you run it, you will get this *very helpful error*:

    In evaluation, the identifier s is either undefined or not an operator.

But s *is* defined, it's a variable right there!

The problem is actually a subtle nuance of assigning to functions. In ``Next``, we're only giving the next state of ``s[1]``. Here are some values of ``s'`` that would satisfy ``Next``:

#. ``<<FALSE, FALSE>>``
#. ``<<FALSE, TRUE>>``
#. ``<<FALSE, 186>>``
#. ``<<FALSE>>``
#. ``0 :> 🌽 @@ 1 :> FALSE @@ 🌽 :> 🌽🌽🌽``

Remember, TLA+ wants you to be as precise as possible. If you didn't specify that ``s[2]'`` is the same as ``s[2]``, it doesn't have to be. TLC naturally considers this an error.

.. index:: 
  single: EXCEPT
  single: @
  seealso: EXCEPT; function

What we actually wanted to write is that ``s'`` is the same as ``s`` *except* that ``s[1]`` is false. Here's the syntax for that:

.. code:: none

  Next == s' = [s EXCEPT ![1] = FALSE]

Yes, I know it's really awkward. No, I can't think of anything better. 

.. tip:: ``EXCEPT`` has some syntactic sugar to make using it more pleasant. First of all, we can assign multiple keys in the same statement:

  .. code-block:: none

    Next == s' = [s EXCEPT ![1] = FALSE, ![2] = 17]

  Second, we can reference the original value of the key with ``@``.

  .. code-block:: none

    IncCounter(c) == 
      counter' = [counter EXCEPT ![c] = @ + 1]

  Finally, we can do nested lookups in the ``EXCEPT``:

  .. code:: none

    Init == s = <<[x |-> TRUE], FALSE>>

    Next == s' = [s EXCEPT ![1].x = ~@]

  PlusCal will naturally convert function assignments to ``EXCEPT`` statements. This means you can use ``@`` in them, too:

  .. code-block:: none

    counter[i] := @ + 1;

Modeling Concurrency
--------------------

Enough with the hour clocks. Let's switch a somewhat more interesting spec: our very very first `threads <threads>` spec.

.. spec:: threads/1/threads.tla
  :ss: threads_1

This is doing basically nothing novel, except that we have two separate processes, meaning that it'll showcase for us how TLA+ handles concurrency. I cleaned up the translation a little, but it should have all these elements:

.. code:: none

  VARIABLES counter, pc

  vars == << counter, pc >>

  ProcSet == (Threads)

  Init == (* Global variables *)
          /\ counter = 0
          /\ pc = [self \in ProcSet |-> "IncCounter"]

  IncCounter(self) == /\ pc[self] = "IncCounter"
                      /\ counter' = counter + 1
                      /\ pc' = [pc EXCEPT ![self] = "Done"]

  thread(self) == IncCounter(self)

  (* Allow infinite stuttering to prevent deadlock on termination. *)
  Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
                 /\ UNCHANGED vars

  Next == (\E self \in Threads: thread(self))
             \/ Terminating

  Spec == Init /\ [][Next]_vars

Looking it at piece-by-piece:

::

  Init == (* Global variables *)
          /\ counter = 0
          /\ pc = [self \in ProcSet |-> "IncCounter"]

``pc`` is defined as a function from process values to labels. Each thread starts at the "IncCounter" label. Then the ``IncCounter`` label is mapped to this:

::

  IncCounter(self) == /\ pc[self] = "IncCounter"
                      /\ counter' = counter + 1
                      /\ pc' = [pc EXCEPT ![self] = "Done"]


The action is only enabled when ``pc[self] = "IncCounter"``, and then as part of it, it sets ``pc[self]`` to "Done". That's how we emulate sequentiality in TLA+ algorith— it's like going from the "IncCounter" label to the "Done" label.

.. tip::

  The PlusCal to TLA+ translator is very simple. If we were writing the TLA+ from scatch, we could use a helper action to these transitions look cleaner:

  ::

    Trans(state, from, to) ==
      /\ pc[state] = from
      /\ pc' = [pc EXCEPT ![state] = 2]

    IncCounter(self) ==
      /\ Trans(self, "IncCounter", "Done")
      /\ counter' = counter + 1

::

    Next == (\E self \in Threads: thread(self))
             \/ Terminating

Concurrency is "just" saying there exists an element of the Thread set where ``thread`` is true. And that's it! That's how you get concurrency!

.. We can of course do more "interesting" kinds of concurrency with slightly different setups. 

To see how ``await`` statements are modeled, let's look at how TLA+ translates `await lock <threads_3>`:

::

  GetLock(self) == /\ pc[self] = "GetLock"
                   /\ lock = NULL
                   /\ lock' = self
                   /\ pc' = [pc EXCEPT ![self] = "GetCounter"]
                   /\ UNCHANGED << counter, tmp >>

So ``await lock`` just becomes ``/\ lock = NULL``.

.. index:: fairness_TODO_sync

Fairness in TLA+
=================

That leaves just one topic left to discuss: how we model `fairness` in pure TLA+. First, one last last operator to introduce: ``ENABLED A`` is true if ``A`` *can* be true this step, ie it can describe the next step.


How fairness can go wrong
-------------------------

.. I'm just gonna put this whole thing in a warning block.

A TLA+ Spec From Scratch
=========================

Strong Fairness
---------------

For this spec, we have a worker doing some abstract job. It can succeed or fail. If it fails, it retries until it succeeds. We make both ``Succeed`` and ``Retry`` weakly fair and leave ``Fail`` unfair. 

.. code-block:: none

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

Why use TLA+?
=============

SO now that we have a brief overview of TLA+, let's double around to a basic question: *why bother*?
What you can do with TLA+:

  * Multiple actions simutaneously
  * Or
  * Strong fairness on branches
  * Refinement (next chapter)
  * Refactoring actions

TODO

.. _Specifying Systems: https://lamport.azurewebsites.net/tla/book-02-08-08.pdf
.. [#plus] The "plus" is for the addition of ZF set theory.
