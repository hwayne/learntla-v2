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

You can also use history variables to track past information no longer present in the system. For example, say you have clients querying a database, which can be updated in the middle in the request. You could add a variable called ``aux_client_request_value`` that is updated *as soon as the client makes the request*, so that updating the database value doesn't lose the information about what the value was at the time of the request.


.. todo:: message pool, seen messages

.. tip:: As a rule of thumb, the spec behavior should not depend on a history variable. If it does, then it's state information the machine you're making has access to, so should be lifted from an auxiliary variable to a real one.

Error Variables
----------------

Let's say you're writing a PlusCal spec with an ``either`` branch::

  either
    \* path 1
  or
    \* path 2
  or
    \* ...

It can be hard to tell in the error trace which branch was taken; you have to infer it from the state change. To get around this, people sometimes add lots of labels::

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

  `ALIAS <ALIAS>`
    If you just want to compute something directly from the state.

Bounding Variables
---------------------

We already saw one of these in our ``reader_writer`` spec. We never let any process write to a queue forever; we always had them write at most N messages. This is because, if they could write forever, we'd have an unbound state space!

One way I like to use bounding variables is to introduce a *small* error into the system. If I want to model dropping messages, I'll write it as

::

  either
    queue := Append(queue, msg);
  or
    await aux_drops_left > 0;
    aux_drops_left := aux_drops_left - 1;
  end either;

(See :doc:`state machines <state-machines>` for a description of how the ``either await`` pattern works.)

Then I can test the system with no drops, or only one drop. The system will not be able to drop every single message.


Prophecy Variables
---------------------

Prophecy variables dictate something will happen *in the future*. Effectively they're a way of pushing nondeterminism earlier in your spec. For example, in the `calculator spec <calculator_1>`, I represented nondeterministically adding numbers like this:

::
  
  Digits == 0..9

  (* --algorithm calculator
  variables 
    i = 0;
    sum = 0;

  begin
    Calculator:
      while i < NumInputs do
        with x \in Digits do
            \* Add
            sum := sum + x;
        end with;
        i := i + 1;
      end while;

There's only one starting state, but each state branches 10 times at every loop iteration. We could instead write

::

  variables 
    i = 1;
    sum = 0;
    aux_proph_digits \in [1..NumInputs -> Digits];

  begin
    Calculator:
      while i <= NumInputs do
        sum := sum + aux_proph_digits[i];
        i := i + 1;
      end while;

Now there's more starting states, but only one possible behavior from each starting state. 

Prophecy values tend to be fairly rare. They're mostly used for making `refinements <refinement>`.

.. prophecy variables, reduce nondeterminism


.. todo:: Economy variables

Usage Notes
===============

When using aux vars, you should make it clear what are "machine" variables that are part of the system and what are auxiliary variables that aren't part of it. If you can't implement something then your spec shouldn't depend on it!

Aux vars can be fiddly in raw TLA+, as they need to be included in ``UNCHANGED`` statements.  You can use sequences to help with this. 



