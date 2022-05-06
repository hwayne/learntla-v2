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


Invariants aren't really part of TLA+. There's no concept of an "invariant" that's treated as special by TLA+. The model checker, TLC, gives us that, but more that's due to pramgatics and efficiency than "invariants" being something deeply important. Rather, TLA+ provides a *general principled* way to write all kinds of different properties, where invariants are just one of many things we can check. To write these, we a set of :dfn:`temporal operators` to describe logical statements across time. We call the broad class of all properties :dfn:`temporal properties`.

There are two kinds of temporal properties: "safety" properties say our system doesn't do bad things. "liveness" properties say our system always does a good thing. "We do not violate any database constraints" is safety, "All transactions either complete or roll back" is a liveness property. All invariants are safety properties, but not all safety properties are invariants. For example:

.. spec:: liveness/1/orchestrator.tla

"There is at least one server that's always online" could mean one of two thigns:

1. At any given point in time, there is at least one server online.
2. In every behavior, there is a particular server, and *that* server is online at all points in time.

(1) is a standard invariant. (2) is a safety property, but **not** an invariant. There is no individual state, by itself, that would violate it. Say I give you the state ``online = {1}``. Is that a violation? *Only* if, in the behavior, there's another state where ``1 \notin online``. So we can't just look at a single state to know if we've broken (2) or not.

TLC can check (2) as a temporal property. To do this we'll need a new operator.

.. index:: []
  :name: always

[]
-----

``[]P`` means that ``P`` is true in every state. When on the outside of a predicate, this is equivalent to an invariant, and in fact is how TLC supports them: writing ``INVARIANT P`` is the same as writing ``PROPERTY []P``. 

Things get more interesting when ``[]`` is part of a larger expresion. Writing ``[]P \/ []Q`` means every behavior has either P or Q as an invariant, but doesn't need to have both. Or we could write ``[]P => []Q``, to say that P is a *stronger* invariant than Q: We can also put it inside quantifiers. To properly model (2), we could write::

  Safety == \E s \in Servers: [](s \in online)

At the beginning of the behavior, we pick one online server. That server is then *always* online. This isn't true, as we see if we check it with ``PROPERTY Safety``.

.. todo:: image of the change

.. note:: this is evlaauted at hte beginnieng of hte temporal poperties, which is why it's ewird if you leave the square out.

::

  State 1: online = {"s1", "s2"}

  State 2: online = {"s2"}

  State 3: online = {"s1", "s2"}

  State 4: online = {"s1"}

  State 5: online = {"s1", "s2"}

In summary, adding ``[]`` to the language lets us represent all invariants, and a host of other properties too.


Stuttering and Fairness
------------------------

``[]`` is just a logical operator, like any other, meaning we can combine it with other logical operators. ``[]~P`` means that P is always not true. ``~[]P`` means that P isn't *always* true. There are two things that could mean:

1. In every behavior, there is at least one state where P is false
2. There is at least one behavior which has at least one state where P is false.

Version (1) is more often useful in specs, so that's what ``~[]P`` formally means. [#ctl]_ If we write

.. spec:: liveness/3/orchestrator.tla
  :diff: liveness/1/orchestrator.tla
  :language: diff

This is a *liveness* property, not a *safety* property. In order to satisfy ``Liveness``, the behavior has to *reach* a state where the server is offline.

We'd expect that to pass. The orchestrator can do one of two things: remove an existing server from ``online`` or add one that's not in it. So if all the servers start online, then eventually we'll remove one, right?

.. index:: stuttering
  :name: stuttering

Not so fast! There's a *third* thing the orchestrator can do: it can crash. In TLA+, any behavior is allowed to :dfn:`stutter`, or make a new state where nothing happens and all variables are unchanged. This includes stutter-steps, meaning any behavior can stutter infinitely, aka crash. And that's exactly what we see if we run the spec with ``PROPERTY <- Liveness``:

.. todo:: trace

.. note:: Why haven't we see this before? Because up until now we've only had invariants, which are only violated by "bad states": partiuclar configurations of variables that break the invariants. Stutter steps don't change the values of anything, so a stutter step can never break an invariant. Here's the first time it can break things by *preventing* us from reaching a good state.

TLA+ allows infinite stutter steps because it is fundamentally a worst-case scenario language. IN reality, systems always crash. If we do not *explicitly say* a system can't crash, TLA+ will assume the system can crash at the worst possible time.

So we need a way to say "don't assume this system can crash". We do this by saying it's a :dfn:`fair process`.

.. spec

This makes the process :dfn:`weakly fair`: it cannot "stop forever". Once we add this change, we see ``Liveness`` holds. There's also **strong** fairness. But this easier to explain (and more useful) in pure TLA+, as opposed to PlusCal. I'll leave the PlusCal material in an advanced topic here.

.. todo:: .. advanced-topic: Strong Fairness

  Weak fairness says that if a process can *always* make progress, it will eventually make progress. Strong fairness is that if a process can *always intermittently* make progress, it will eventually make progress. To see the difference, consider this model of several threads sharing a lock:

  .. spec

  When in ``AwaitLock``, each thread can only get the lock if ``lock := Null``. So it's only *intermittently* able to progress. Since every thread with the lock is gauranteed to release it, it's *always intermittently* able to progress. In weak fairness, if we have five threads, we can't guarantee that all five threads will eventually get the lock; one could get starved out.

  .. error trace

  We can make the processes strongly fair by writing ``fair+``. Then every thread will eventually get the lock. We can also make indiviudal actions strongly fair, by writing ``AwaitLock:+``.

.. tip::
  
  Not every process in a spec needs to, or should be, fair. Consider a spec where one process represents the worker and one represents a user. The user actions aren't *guaranteed* to happen: the user can always step off the computer and go outside.

.. todo:: make an advanced-topic directive that's either a dropdown or a popout. And it should do an include

.. todo:: explain difference between stutter and an action that does nothing. It matters for deadlocks only

.. index::
  single: <>
  see: eventually; <>

.. _eventually:

<>
------

While ``~[]P`` has some interesting properties, we rarely write it. It's not often we need to check that something "is sometimes" not true in our system. What *is* useful is writing ``~[]~P``: "Sometimes 'not P' is false", or "Sometimes P is true". This means that P isn't an invariant in all states, but must hold in *at least one* state. 

Because "Not always not P" is a mouthful, we have a separate operator that means the same thing: ``<>P``, or "Eventually P". We've already been crudely simulating "eventually" properties before, in duplicates and `threads`. Here's the correctness condition for threads:

::

  AllDone == 
    \A t \in Threads: pc[t] = "Done"

  Correct ==
      AllDone => counter = NumThreads


The ``AllDone =>`` is just a precondition that ``counter = NumThreads`` is true at the end of the algorithm execution. Using ``<>`` we can rewrite it as a temporal property:

.. spec:: threads\liveness_1\threads.tla
  :diff: threads\3\threads.tla

(Remember this is checked under "Temporal Properties", not "Invariants"!)

When we run this with ``PROP Liveness, NULL <- [mv]`` the spec fails due to stuttering. There's no guarantee the threads will finish running, because they're unfair. This *wasn't* a problem with ``Correct`` before because that only says that *if* we reach the end, *then* the answer is correct. It still passes if we never reach the end!

Making the threads fair makes this pass :ss:`threads_liveness`:

.. spec:: threads\liveness_2\threads.tla
  :diff: threads\liveness_1\threads.tla

.. index:: <>[]

In one way, ``Liveness`` is more accurate than ``Correct``. In another way, though, it's *less* accurate. Here's a bug that wouldn't pass ``Correct``:


.. spec:: threads\liveness_3\threads.tla
  :diff: threads\liveness_2\threads.tla

When we're done, ``counter = 3``... but ``Liveness`` still passes! This is because ``<>(counter = 2)`` is true if ``counter = 2`` in *at least one state* of the behavior. It doesn't matter if we then change *away* from that, because it's been true at least once.

Fortunately, our temporal operators are extremely flexible, and we can compose them together. If ``[]P`` means "P is always true", and ``<>P`` is "P is eventually true", then ``<>[]P`` is "eventually P is always true". P can start out false, but after some point in every behavior, it will forevermore be true.

.. spec:: threads\liveness_4\threads.tla
  :diff: threads\liveness_3\threads.tla

This now fails, as ``counter`` doesn't stay as 2.

.. tip::

  You can also write ``[]<>P``: "P is always eventually true". In the threads spec, this has the same outcome, but there are cases where it's broader than ``<>[]P``. For example, in an hour clock, ``[]<>(time = midnight)`` is true, but ``<>[](time = midnight)`` is false.


.. todo:: inkscape of the three different uses of ``<>``

.. index::
  single: ~>

.. _leads_to:
.. _~>:

~>
------

The last operator is ``~>``. Recall that ``P => Q`` preconditions Q on P: if P is true, then Q is also true. ``P ~> Q`` is the temporal analog: if P is true, then Q is *eventually* true (now or in a future state).

.. todo:: better example?

Say we have a set of tasks described by ``TaskType``, an ``inbound`` pool of type ``SUBSET TaskType``, and a set of workers with their own task sets. A property of this system might be that every inbound task is eventually processed by a worker. You can represent this with ``~>``:

  ::

    Liveness ==
      \A t \in TaskType:
        t \in inbound
          ~> \E w \in Workers:
            t \in worker_pool[w]

.. note:: ``P ~> Q`` is triggered *every* time P is true. Even if the formula was satisfied before, if ``P`` becomes true again, then ``Q`` has to become true again too.

.. todo:: an example

Using Temporal Operators
----------------------------

Temporal properties are incredibly powerful. There's some things you need to keep in mind, though:

* Don't try to be too clever.

It takes TLC significantly longer to test liveness properties than safety ones.

You cannot use `symmetry sets <model_set>` with liveness properties.


Summary
=========

.. [#ctl] CTL vs LTL logic, explain

.. .. exercise::

  Just as predicate logic has tautologies, so does temporal logic. Informally explain why these tautologies are true:

  #. ``~<>~P = []P`` (``~(~[]~)~P``)
  #. ``<>(P \/ Q) = <>P \/ <>Q``
  #. ``[](P /\ Q) = []P /\ []Q``

  #. ``\A x \in S: []P(x) = [](\A x \in S: P(x))``
  #. ``\E x \in S: <>P(x) = <>(\E x \in S: P(x))``



