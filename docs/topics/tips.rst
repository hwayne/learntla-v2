.. _topic_tips:

############
General Tips
############



General small things for writing better specs.


Both TLA+ and PlusCal
======================


Use ASSUME
-----------

Every ``CONSTANT`` should have an ``ASSUME`` to communicate what values are expected of the constant. For model values, it usually suffices to make the ``ASSUME`` say it's *not* part of a set. To say something is a certain data type, compare it to the empty value of that type. If it's *not* that type TLC will crash the ``ASSUME``, which serves the same purpose as it legitimiately failing.

::

  CONSTANT Threads, NULL
  ASSUME Threads # {}
  ASSUME NULL \notin Threads

From this it's clear that Threads is a set and NULL is not a thread.

.. todo:: Using ASSUME for operators


Model tagged unions with structs
-------------------------------------------

TLC can't have a set of strings and integers. If you need that, you can instead use structs with a ``type`` and ``val`` field.

::

  {
   [type |-> "int", val |-> 1], 
   [type |-> "str", val |-> "1"] \* ok
  }


.. _decompose_structs:

Decompose functions of structs
------------------------------

I often see people encode variables that are functions of structures:

::

  VARIABLE state
  WorkerState == [queue: Seq(Msg), online: BOOLEAN]
  Types ==
    state \in [Worker -> WorkerState]
  
  \* ...


This more closely matches how we do things in programming languages. It's harder to work with in TLA+, though, because you can only update a variable once per step. So if you want to both ``online`` *and* ``queue`` in one step, you have to do them in the same expression. ie you can't write

::

  Label:
    state[w].online = FALSE;
    state[w].queue = <<>>;

It's easier to instead break the variable into two other variables, like this:

::

  VARIABLES worker_queue, worker_online

  Types ==
    /\ worker_queue \in [Worker -> Seq(Msg)]
    /\ worker_online \in [Worker -> BOOLEAN]

  \* ...

Then you can update ``worker_queue`` and ``worker_online`` separately.

The downsides of this are 1) when working in pure TLA+, your ``UNCHANGED`` statements get a bit more cluttered, and 2) it's a little further from what your implementation will look like. But the upsides are enough to make it worth it.

In general, I mostly use structures for immutable values, like the bodies of messages.

Separate Safety and Liveness Models
-------------------------------------

.. todo:: {CONTENT} more on model optimization

Since liveness properties take a lot longer to check (and can't use `symmetry sets <symmetry_set>`), I use a separate model for just checking liveness properties, which uses smaller constants.

Use the extra space in a module
--------------------------------

All modules have to take the form

::

  \* top area
  ---- MODULE name ----
  \* actual module
  ====
  \* bottom area

Everything in the top space and the bottom space is ignored. I like using the bottom area as a "scratch space" and put various TLA+ code there. I use the top area to write more about the problem domain and requirements we're trying to model, as well as information about the spec itself.

More recently I've been experimenting with putting configuration data in the top area, which I then target with scripts. I used that to generate a lot of the `spec diffs <https://github.com/hwayne/learntla-v2/tree/master/raw-specs>`__ for this guide.

THEOREM
-------

TLA+ has a ``THEOREM`` keyword, which *ostensibly* declares the properties of the spec:

::

  THEOREM Spec => []TypeInvariant

This doesn't do anything to the model checker, but it can be useful for documenting the properties of your system.

TypeInvariants and ModelInvariants
-----------------------------------

We've used TypeInvariants a lot already. They're a good invariant for any system, and it's good to always cover all of your variables in TypeInvariants. As a principle, I like the TypeInvariant to only cover the *possible* values of a variable, as opposed to the *legitimate values*. IE if two sets of numbers have to be disjoint, I'd split that into two invariants:

::

  TypeInvariant ==
    /\ set1 \subseteq Int
    /\ set2 \subseteq Int

  SetsAreDisjoint ==
    /\ set1 \intersect set2 = {}

I wouldn't put ``SetsAreDisjoint`` into my TypeInvariant because I see that more as a "correctness" property of the system instead of just a bounds-check.

Model invariants are like TypeInvariants, except that they used to check the state space is finite. For example:

::

  CONSTANTS MinInt, MaxInt
  ASSUME {MinInt, MaxInt} \subseteq Int

  ModelInt == MinInt .. MaxInt
  ModelInvariant ==
    /\ set1 \subseteq ModelInt
    /\ set2 \subseteq ModelInt

Then you can write your spec to satisfy ``ModelInvariant``, or at a `state constraint <state_constraint>` to your model runs.

.. Latchkeys and tripwires 

  Maybe that's its own topic

PlusCal
===========

.. todo:: How to use assert

Use macros
-------------

`Macros <macro>` are your main form of statement reuse in PlusCal.

While loops considered harmful
--------------------------------

A `while` loop creates a new state for *every* loop iteration, adding a lot of concurrency and state-space explosion to your spec. Sometimes this is what you want, when say reading from a queue. But I often see beginners use while loops to do *computations*, like this:

::

  Double:
    while i <= Len(seq) do
      seq[i] := seq[i] * 2;
      i := i + 1;
    end while;

Instead, reassign the entire sequence in one step:

::

  Double:
    seq := [i \in 1..Len(seq) |-> seq[i] * 2];

State sweeping
--------------

Discussed `here <state_sweeping>`.

TLA+
===========

Managing UNCHANGED
------------------

If you have a lot of variables, `UNCHANGED` statements get unweildy quickly. Fortunately, you can group variables as sequences and then use UNCHANGED on a sequence of groups. 

::

  VARIABLE worker_queue, worker_online
  VARIABLE topic_subscribers, topic_id

  worker_state == <<worker_queue, worker_online>>
  topic_state == <<topic_subscribers, topic_id>>

  SomeAction ==
    /\ x' = x + 1
    /\ UNCHANGED <<worker_state, topic_state>>


Helper Actions
---------------

It's okay to split the next-state relations across multiple actions. One thing I do a lot is write a helper to update ``pc``:

::

  Trans(agent, a, b) ==
    /\ pc[agent] = a
    /\ pc' = [pc EXCEPT ![agent] = b]

Then I can write ``Trans(agent, "state1", "state2")`` inside another action.


@
------

In a function update, ``@`` refers to the old value.

::

  \* Verbose
  f' = [f EXCEPT ![1][2].a = f[1][2].a + 1]

  \* Clean
  f' = [f EXCEPT ![1][2].a = @ + 1]

Parameterize your actions
-------------------------

Instead of

::

  Add ==
    \E w \in Worker: s' = s \union {w}

  Remove ==
    \E w \in Worker: s' = s \ {w}

  Next == Add \/ Remove

Write

::

  Add(w) == s' = s \union {w}
  Remove(w) == s' = s \ {w}

  Next ==
    \E w \in Worker:
      \/ Add(w) 
      \/ Remove(w)

Move the ``\E`` to the bottom layer and pass a value into your actions. This is better because it lets you *reuse the same value* in multiple actions. Say you want to log every worker that's added or removed. You can't easily do this in the first version of the spec, but in the second you could write 

::

  Log(w) == log' = Append(log, w)

  Next ==
    \E w \in Worker:
      /\ \/ Add(w) 
         \/ Remove(w)
      /\ Log(w)

.. _action_refactoring:

Refactor with Action Properties
--------------------------------

If we're simplifying an action, we want to make sure that our simplification doesn't change it.

::

  OldAction(user) ==
    seq' = seq \o <<user>>
  
  NewAction(user) ==
    seq' = Append(seq, user)

We can check that by adding an `action property <action_property>` that checks the two are equivalent:

::

  RefactorProp == [][
    \A u \in User:
      OldAction(user) = NewAction(user)
  ]_vars

If we're trying to *expand* an action, then we only care that ``NewAction`` does a superset of the things ``OldAction`` does. In that case, we can loosen our requirements by using ``=>`` instead of ``=``.
