.. _chapter_temporal_logic:

##########################
Temporal Properties
##########################

- Termination
- Weak Fairness
- Stuttering
- Liveness 
- <> [] ~>
- Uses
- Warnings


.. invariants aren't really part of TLA+. There's no special concept of an invariant, that's just a sugar TLC gives us, so we can say "P is an invariant", that decompiles to a temporal property "[]P is a property".

  Wait, what? That's because invariants are too limited. TLA+ can specify properties on *behaviors*, not just *all states in a behavior*.


.. orchestrator spec

"There is at least one server that's always online" could mean one of two thigns:

1. At any given point in time, there is at least one server online.
2. In every behavior, there is a particular server, and *that* server is online at all points in time.

(1) is a standard invariant. (2) is **not** an invariant. There is no individual state, by itself, that would violate it. Say I give you the state ``online = {1}``. Is that a violation? *Only* if, in the behavior, there's another state where ``1 \notin online``. So we can't just look at a single state to know if we've broken (2) or not.

Here's how we'd write these as temporal properties:

1. ``Safety1 == [](\E s \in Servers: s \in online)``
2. ``Safety2 == \E s \in Servers: [](s \in online)``

Notice that in (1), we have the ``[]`` wrapping the entire quantifier. That;s how you know it's an invariant. In (2), the ``[]`` is *inside* a quantifier. 

``Safety2`` is also *stronger* than ``Safety1``: if it holds, we know that ``Safety1`` also holds. You can reason this through mathematically, or we could use TLC to check that.

.. =>

In summary, adding ``[]`` to the language lets us represent all invariants, and a host of other properties too.

* ``[]`` is just a logical operator, like any other, meaning we can combine it with other logical operators.

Stuttering and Fairness
------------------------

``~[]P`` means that "P isn't always true", or "there is a state where P is not true." Let's add TK to TK

P

Now, you'd expect this ot 

Liveness
===============

Take the following spec and translate it to TLA+:

.. spec:: termination/1/counter.tla

Simple spec. At this point should be able to epxress that when the algorithm finishes, x = 3. Here's a spec that *also* guarantees the invariant "when the spec finishes, x = 3": 

.. spec:: termination/2/counter.tla

If we never reach the end state, then it doesn't matter what we say about the end state, it's always gona be true! In fact, there isn't a single invariant that (1) will pass that (2) won't also pass. 

But there are properties that are only true of (1), they're just not invariants. For example, (1) will eventually run to completion, while (2) runs forever. In other words, (1) **terminates**. This is not an invariant because it isn't a property of individual states of the spec. Rather, it's a property of individual *behaviors*: each behavior is guaranteed to completion.

We can learn how to specify this by looking at the TLA+ translation of the spec. Near the very end you will see this line::

  Termination == <>(pc = "Done")

.. index:: <>

The key difference is the ``<>``. It's sometimes called the "diamond operator", but more often **eventually**. ``<>P`` means that "at *some* point, ``P`` is true". It could be true right now, or it could be true 10,000 steps from now, but it will *eventually* be true.

This makes Termination a **temporal property**.

With an invariant violation, TLC finds a behavior that eventually reaches a *bad state*. With ``Termination`` violation, TLC finds a behavior that's doesn't reach a good state. For this reason we often call these "Safety" and "Liveness" {{}}. Since these are checked in different ways, we put them in different sections of the model checker. You'd put ``Termiantion`` under "Temporal Properties".

.. warning:: Leaving out the temporal mode

If we run this on (2), we get the following error:

  Temporal properties were violated.

.. note:: Due to historical implementation details TLC cannot tell us which temporal property is violated, but this is something we want to fix in the near future.

``Termination`` successfully shows that (2) never completes. Just to be on the safe side, let's run the same property on (1) and confirm it works.

.. todo:: Find a clean way to introduce liveness term

  Temporal properties were violated.

...huh. So (1), despite *obviously* being a complete spec, is failing the same check. Let's look at the error trace.

State 1: x = 0

State 2: x = 1

State 3: x = 2

State 4: x = 3

State 5: Stuttering

.. index:: stuttering
.. index:: stutter-invariance

Stuttering and Fairness
-----------------------


To understand what's going on here, I need to provide a bit of context.

You might have noticed that all of our specs so far are in a single file. Unlike with programming, composing specifications is *very* difficult— not just in TLA+, in *all* specifications languages. One of the things that makes it (*somewhat*) easier is **stutter-invariance**. A "stutter-step" is when a behavior has a state "transition" that leaves all the values unchanged. If you can insert a stutter step between *any* two steps without it breaking your spec, then your spec is "stutter-invariant". All TLA+ specs are stutter-invariant by definition: it's baked into the language formalism. We'll talk about how this happens `later <todoblar>`

We haven't seen stutter steps before because stutters *cannot* break invariants. Invariants are boken by reaching bad states. But a stutter step doesn't move you to a new state, so it's not a problem. But stutter steps *can* break liveness properties. If we insert an infinite number of stutter steps at ``x := 2``, we never reach ``Termination``.

You may think this is weird, but it ends up being extremely useful. "The program stutters forever" could represent the computer crashing, or a response never returning, or the computation simply taking much longer than our time scale. [#scale]_ Above all, TLA+ asks us to be *explicit* about what we mean. So if we want to assume an algorithm doesn't crash, we have to explicitly *declare* the algorithm doesn't crash.

In Pluscal, we can make an algorithm *must* make progress if it can writing ``--fair algorithm`` instead of ``--algorithm``. This makes the spec weakly fair. More specifically, if a weakly fair action is always enabled, it eventually happens.

.. spec here

We can also make individual processes weakly fair, by writing ``fair process``. In the following spec, ``<>(x = 3)``.

.. spec here

.. rubric:: Strong Fairness


I said ``fair`` makes the algorithm *weakly* fair. Most of the time, weak fairness is what you need. But we have anothr shade of fairness called *strong* fairness. To see why the distinction matters, let's jump to a different example for a little bit. This is a variation of the `threads` specs we wrote back when talking about concurrency.

.. spec here

Both threads are weakly fiar: if they can always make progress, they are guaranteed to make progress.


Liveness Properties
====================

``<>`` is useful on its own, but to really reach the full potential of temporal properties, we need one more operator.

Here's a simple specification for a clock:

.. spec

Unlike our previous specs, we *do not* expect this one to terminate. We do, however, expect it to keep looping through every possible hour value. It should reach ``hour = 0`` an infinite number of times. How do we express that as a property?

You might try ``<>(hour = 0)``, but this only says that we're at midnight *at least once* in every behavior. If the clock ticks past midnight *and then stops*, ``<>(hour = 0)`` is still satisfied. We want to instead say that ``hour = 0`` an *infinite number of times*. Or, more formally, at every point in a behavior, there is a future state where we're at midnight. If we tick past midnight, there must be another future state where we're back at midnight again.

.. index:: []

Speciying this requires the other temporator: ``[]``, or "always". ``[]P`` means that P is true in every state of every behavior. On its own ``[]`` is not that useful to use, because saying ``[]P`` is a property is the same as saying ``P`` is an invariant. 

.. note:: Technically speaking, ``<>`` is defined in terms of ``[]``: ``<>P == ~[]~P``.

.. exercise:: Show that ``[]P == ~<>~P``.

  .. First define ``Q == ~P``. ``<>Q == ~[]~Q``, ``~<>Q == []~Q`` ``~<>~~Q == []~Q``, ``~<>~P == []P``.

But *combine* it with ``<>`` and we get a lot more power. ``[]<>(hour = 0)`` means "at all points in every behavior, there is a future point where the hour is midnight," which is exactly what we want. You can read the ``[]<>`` as "always eventually".

We can also combine things the other way. ``<>[](hour = 0)`` means "eventually, there is a point where it is forevermore midnight." Check that our spec fails this. ``<>[]``

.. exercise:: Explain *informally* why ``<>[]P => []<>P`` (if P is eventually always true, then it is always eventually true.)

  .. Blah blah blah



Putting it into practice



.. [scale] If an algorithm is supposed to take 10ms to run, then infinite stuttering could represent it completing in 1000x the time, or 10s.
