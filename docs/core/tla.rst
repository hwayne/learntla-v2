.. _chapter_tla:

########
TLA+
########

PlusCal is a formalism designed to make using formal methods easier. By learning PlusCal first, we can focus on teaching first logic and model checking, leaving temporal logic for later. Another advantage is that can bootstrap TLA+ from it by looking at what the PlusCal generates, and infer the TLA+. We know that the PlusCal generated is valid TLA+, so we can use it to understand the TLA+.

.. index:: action

There are two concepts in the :doc:`last chapter <action-properties>` that you should review in order to understand TLA+:

* The prime operator: ``x'`` is the value of x *in the next state*.
* The box operator: ``[P]_x`` is ``P \/ UNCHANGED x``.

Now let's learn us some TLA+!

Learning from PlusCal
======================

I find the easiest way to explain what's going on with TLA+ is to relate it to what the PlusCal does. In his original book `Specifying Systems`_, Leslie Lamport introduces TLA+ with a specification of an hour clock, and I'd be remiss to break with tradition. The PlusCal is a *mostly* faithful translation of his TLA+ spec.

.. spec:: tla/hourclock_1/hourclock.tla
  :ss: hourclock_1

You should be able to look at this spec and run it in your head. ``hr`` starts at 1, and then increment, wrapping at 12 back to 1. The TLA+ translation *must* do the same thing. Let's take a look at it:

::

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

In ``Next``, we've replaced ``hr := 1`` with ``hr' = 1``. As we learned in the :doc:`last chapter <action-properties>`, ``hr'`` is the value of ``hr`` in the *next* state. ``hr' = 1`` is a *boolean* statement, which is true or false. In fact, ``Next`` is a boolean operator: it's either true or false. It is true if it accurately describes the value of ``hr`` in the next state, and false if it does not.

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

::

  Spec == Init /\ [](Next \/ UNCHANGED vars)

By convention, in a temporal formula, anything outside a temporal operator (`[] <always>` or `<> <eventually>`) is tested as true in the initial state. So ``Spec`` is true iff:

* In the initial state, ``Init`` is true, and
* ``Next \/ UNCHANGED vars`` is always true in every step.

Since ``Next`` is an action, to be "always true" it must always accurately describe the new values of the system. Formally, we call it the :dfn:`Next State Relationship`. This gives us the blueprint for what spec is.

.. todo:: {INKSCAPE} Graph showing valid and invalid specs

.. note::

  Technically speaking, we can use TLA+ to describe **any possible set of behaviors**. This is technically a valid spec:

  .. code-block:: none

    Init == x = 1
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

::

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

::

  Next == IF hr = 12
             THEN /\ hr' = 1
             ELSE /\ LET x == 1 IN
                       hr' = hr + 1



Okay, that's done through a `LET`, which makes sense. It's a 1-1 translation. It also explains why you can't put labels inside a ``with`` statement, since ``LET`` is just a temporary binding.

Now for nondeterministic with:

.. spec:: tla/hourclock_4/hourclock.tla
  :diff: tla/hourclock_3/hourclock.tla

::

  Next == IF hr = 12
             THEN /\ hr' = 1
             ELSE /\ \E x \in 1..2:
                       hr' = hr + x

This is more interesting! We "assign" ``hr'`` inside the quantifier.

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

Remember, TLA+ wants you to be as precise as possible. If you didn't specify that ``s[2]'`` is the same as ``s[2]``, it doesn't have to be. TLC automatically considers this an error.

.. index::
  single: EXCEPT
  single: @
  seealso: EXCEPT; function

What we actually wanted to write is that ``s'`` is the same as ``s`` *except* that ``s'[1]`` is false. Here's the syntax for that:

::

  Next == s' = [s EXCEPT ![1] = FALSE]

In ``![1]``, ``!`` is the "selector" and ``[1]`` is the element. So this creates a copy of s, looks up ``copy_s[1]``, replaces that value with ``FALSE``, and assigns the whole mess to ``s'``.

Yes, I know it's really awkward. No, I can't think of anything better.

.. tip:: ``EXCEPT`` has some syntactic sugar to make using it more pleasant. First of all, we can assign multiple keys in the same statement:

  ::

    Next == s' = [s EXCEPT ![1] = FALSE, ![2] = 17]

  Second, we can reference the original value of the key with ``@``.

  .. code::

    IncCounter(c) ==
      counter' = [counter EXCEPT ![c] = @ + 1]

  Finally, we can do nested lookups in the ``EXCEPT``:

  .. code::

    Init == s = <<[x |-> TRUE], FALSE>>

    Next == s' = [s EXCEPT ![1].x = ~@]

  PlusCal will naturally convert function assignments to ``EXCEPT`` statements. This means you can use ``@`` in them, too:

  .. code::

    counter[i] := @ + 1;

Modeling Concurrency
--------------------

Enough with the damn clocks. Let's switch a somewhat more interesting spec: our very very first `threads <threads>` spec.

.. spec:: threads/1/threads.tla
  :ss: threads_1

This has two separate processes, meaning that it'll showcase for us how TLA+ handles concurrency. I cleaned up the translation a little, but it should have all these elements:

::

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


The action is only enabled when ``pc[self] = "IncCounter"``, and then as part of it, it sets ``pc[self]`` to "Done". That's how we emulate sequentiality in TLA+ algorithm— it's like going from the "IncCounter" label to the "Done" label. Each label corresponds to exactly one action, and vice versa.

.. _trans:
.. tip::

  The PlusCal to TLA+ translator is very simple. If we were writing the TLA+ from scatch, we could use a helper action to these transitions look cleaner:

  ::

    Trans(state, from, to) ==
      /\ pc[state] = from
      /\ pc' = [pc EXCEPT ![state] = to]

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

So ``await lock = NULL`` just becomes ``/\ lock = NULL``.

.. index::
  single: fairness; in TLA+
  single: WF_vars
  single: SF_vars
  single: ENABLED


Fairness in TLA+
=================

That leaves just one topic left to discuss: how we model :ref:`fairness <fairness>` in pure TLA+. First, two final keywords to introduce:

1. ``ENABLED A`` is true if ``A`` *can* be true this step, ie it can describe the next step.
2. ``<<A>>_v`` means that ``A`` is true *and* v changes. Compare to ``[A]_v`` being "``A`` is true *or* v doesn't change".

Fairness is formally defined in TLA+ as follows::

  WF_v(A) == <>[](ENABLED <<A>>_v) => []<><<A>>_v
  SF_v(A) == []<>(ENABLED <<A>>_v) => []<><<A>>_v

In English:

* ``WF_v(A)`` (A is weakly fair): If it is *eventually always* true that the A action *can happen* (in a way that changes v), then it *will* eventually happen (and change v).
* ``SF_v(A)`` (A is strongly fair): If it is *always eventually* true that the A action *can happen* (in a way that changes v), then it *will* eventually happen (and change v).


Fairness constraints are appended to the definition of ``Spec``. You can see this in the translation of our prior `strong fairness example <strong_fairness_spec>`::

  Spec == /\ Init /\ [][Next]_vars
          /\ \A self \in Threads : SF_vars(thread(self))

(Remember, ``Spec`` defines what *counts as a valid trace*. Fairness is an additional constraint, ruling out things like infinite stutters.)

Notice that by writing ``\A self \in Threads : SF_vars(thread(self))``, we're effectively making every thread fair. If we instead wrote ``\E``, we'd be saying that at least one thread is fair, but the rest may be unfair. If both those conditions are syntactically intuitive to you, I'd say you fully understand how pure TLA+ works.



.. _fairness_status_example:

Fairness is more useful in TLA+
------------------------------------

In pluscal, we can only apply fairness conditions to labels, which correspond to top-level actions. In TLA+, we can apply the fairness condition to subactions, which gives us the branches of labels.

::

  VARIABLES status

  Init == status = "start"

  Trans(from, to) ==
    /\ status = from
    /\ status' = to

  Succeed == Trans("start", "done")
  Fail == Trans("start", "fail")
  Retry == Trans("fail", "start")

  Next == Succeed \/ Fail \/ Retry \/ UNCHANGED status

  Fairness ==
    /\ SF_status(Succeed)
    /\ WF_status(Retry)

  Spec == Init /\ [][Next]_status /\ Fairness

  Liveness == <>(status = "done")

  ====

This spec can fail an arbitrary number of times, but is guaranteed to eventually succeed.

.. todo::

  {CONTENT} A warning about how machine closure can blow up in your face
  Also an example of fairness in a temporal property

Why use TLA+?
=============

So now that we have a brief overview of TLA+, let's come around to a basic question: *why bother*?  While TLA+ has a steeper learning curve than PlusCal, it also has a higher power ceiling. There are lots of things you can do in pure TLA+ that would be difficult or impossible to do in PlusCal. Some examples:

* Writing `helper actions <trans>`.
* Using fairness `in subtle ways <fairness_status_example>`.
* Verifying a `refactored spec has the same behavior <action_refactoring>`.
* Interruptable algorithms. Say I have the sequence of steps :math:`Start \to A \to B \to C \to D`, and A,B,C can all "reset" to start. In PlusCal I'd have to model that by duplicated `either <either>` blocks:

  ::

    A:
      either
        \* A step stuff
      or
        goto Start;
      end either;
    B:
      either
        \* B step stuff
      or
        goto Start;
      end either;
    \* ...

  In TLA+, I can more easily write this as

  ::

    \/ \/ A
       \/ B
       \/ C
       \/ D
    \/ pc' = "Start"

* Systems that would map onto having multiple processes in PlusCal with the same values. For example, if each worker can run multiple sequential tasks in parallel.
* :doc:`Refinement properties</topics/refinement>`.

At the same time, it's okay to stick with PlusCal. Plenty of people never learn pure TLA+ and get along fine with just PlusCal. Just know that it has limits, and know when you're pushing against those limits.



.. todo:: Summary

.. _Specifying Systems: https://lamport.azurewebsites.net/tla/book-02-08-08.pdf
.. [#plus] The "plus" is for the addition of ZF set theory.
