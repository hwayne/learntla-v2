.. _topic_aux_vars:

#####################
Auxiliary Variables
#####################


While TLA+ properties have a lot of flexibility, they also have limits. You can't "forget" a property, like say "P is true until Q is true, after while P can be false." Say you write it as "~P => Q". Then if we set ~P and *then* set ~Q, the invariant fails, even though we should have "forgotten" it. 

We can sort of fix this by adding a new variable ``Q_was_true``, then write the property as

::
  
  Prop == P => Q \/ Q_was_true

  Next ==
    /\ \* regular spec
    /\ IF Q' THEN Q_was_true' ELSE UNCHANGED Q_was_true

``Q_was_true`` is called an :index:`auxiliary variable` ("aux var"). By augmenting specs with aux vars we can represent a wider range of systems and check a wider range of properties. It's not the most elegant solution, but it gets the job done.

.. note:: In other formal methods disciplines, auxiliary variables are sometimes called "ghost" or "helper" variables.

There are many different ways to use aux vars. Here are just a few!

Types of Auxiliary Variables
=============================

History Variables
-----------------

Variables that represent something that happened. ``Q_was_true`` is a history variable. If you want to confirm that your history variables don't change once they're set, you can make that an `action property <action_properties>`:

::

  Prop ==
    [][Q_was_true => UNCHANGED Q_was_true]_Q_was_true

You can also use history variables to track past information no longer present in the system. Say you want to make sure that two threads alternate in the critical section, so that neither reaches the critical section twice in a row.

.. message pool, seen messages
.. todo:: Pull the example from Dekker

Error Variables
----------------

Let's say you're writing a pluscal spec with an ``either`` branch::

  either
    \* path 1
  or
    \* path 2
  or
    \* ...

It can be hard to tell in the error trace which branch was taken, you have to infer it from the state change. To get around this, people sometimes add lots of labels::

  either
    Path1:
      \* ...
  or
    Path2:
      \* ...
  or
    \* ...

Then you can see which path you took in ``pc``. But doing this adds a lot of extra concurrency to your spec— at best exploding the state space, at worst changing the spec semantics!

What we want is to enrich the error traces without changing the spec semantics. This is a great place for an aux var.

::

  either
    aux_branch := "Path1";
      \* ...
  or
    aux_branch := "Path2";
      \* ...
  or
    \* ...

Another common use is to keep a historical log of what happened when::

  \E w \in Workers:
    /\ \/ Action1(w)
       \/ Action2(w)
       \/ Action3(w)
    /\ aux_log' = Append(aux_log, w)

.. seealso::

  ALIAS
    If you just want to compute somethig *per state*.

Bounding Variables
---------------------

We already saw one of these in our ``reader_writer`` spec. We never let any process write to a queue forever; we always had them write at most N messages. This is because, if they could write forever, we'd have an unbound state space!


.. prophecy variables, reduce nondeterminism

  Example call will fail

  Very rare, mostly used for refinements
  if aux_proph_will_receipt then


Usage Notes
===============

Don't make the code use them

Aux vars are tricky to use in raw TLA+, as they need to be included in ``UNCHANGED`` statements.  You can use sequences to help with this. 



