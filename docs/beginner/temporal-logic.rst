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

At the beginning of the behavior, we pick one online server. That server is then *always* online. 
.. note:: this is evlaauted at hte beginnieng of hte temporal poperties, which is why it's ewird if you leave the square out.

::

  State 1: online = {"s1", "s2"}

  State 2: online = {"s2"}

  State 3: online = {"s1", "s2"}

  State 4: online = {"s1"}

  State 5: online = {"s1", "s2"}

.. tip:: 

  I'm not going to go into the exact semantics for *how* it works just yet, but ``[](P => []Q)`` says that Q can be false *until* there's a state where P is true, and then Q must be true forever after. This is a tripwire.


.. =>

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

This makes the process :dfn:`weakly fair`: it cannot "stop forever". Once we add this change, we see ``Liveness`` holds. There's also **strong** fairness. But this easier to explain (and more useful) in pure TLA+, as opposed to PLusCal. I'll leave the PlusCal material in an advanced topic here.

.. .. advanced-topic:: Strong Fairness

.. tip::
  
  Not every process in a spec needs to, or should be, fair. Consider a spec where one process represents the worker and one represents a user. The user actions aren't *guaranteed* to happen: the user can always step off the computer and go outside.

.. todo:: make an advanced-topic directive that's either a dropdown or a popout. And it should do an include

.. todo:: explain difference between stutter and an action that does nothing. It matters for deadlocks only

..  index: :
  :single: <>
  :see: eventually; <>
  :name: <>

<>
------

While ``~[]P`` has some interesting properties, we rarely write it. It's not often we need to check that something "is sometimes" not true in our system. What *is* useful is writing ``~[]~P``: "Sometimes 'not P' is false", or "Sometimes P is true". This means that P isn't an invariant in all states, but must hold in *at least one* state. 

Because "Not always not P" is a mouthful, we have a separate operator that means the same thing: ``<>P``, or "Eventually P".


.. exercise::

  Just as predicate logic has tautologies, so does temporal logic. Informally explain why these tautologies are true:

  #. ``~<>~P = []P`` (``~(~[]~)~P``)
  #. ``<>(P \/ Q) = <>P \/ <>Q``
  #. ``[](P /\ Q) = []P /\ []Q``

  #. ``\A x \in S: []P(x) = [](\A x \in S: P(x))``
  #. ``\E x \in S: <>P(x) = <>(\E x \in S: P(x))``

.. [#ctl] CTL vs LTL logic, explain
