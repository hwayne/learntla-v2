.. _chapter_action_properties:

########################
Action Properties
########################

.. index:: Action Properties

.. _action_properties:

Action Properties
==================

In the `last chapter <chapter_temporal_logic>` I said that all invariants are safety properties, but not all safety properties are invariants. Outside invariants, the biggest class of safety properties are action properties, which are restrictions on how the system is allowed to *change*.

Let's play a bit more with the threads spec:

.. spec:: threads/3/threads.tla

.. todo:: write this more gradually

Here are a couple of restrictions on the way the spec should be allowed to change. Some things about this spec:

* ``counter`` should only increase.
* If a thread holds the lock, it *cannot* go to another thread without being unlocked first.

Here's how we write the first as an action property:

::

  [][counter' >= counter]_counter

Wait, *what*?

Don't worry, we'll be going into *painful* detail in the next section. For now, let's confirm that this actually breaks. First make a change where counter decreases:

.. spec

Now run this with ``PROPERTY CounterOnlyIncreases``. If set up right, you should see this error:

.. error

This doesn't fail because we have a state where ``counter = 0``. That's a totally valid state for the spec, and is in fact the starting state! It fails because ``counter = 1`` *and then becomes 0*. It's the fact *counter decreases* that's an error.

.. index:: Box Action Formula, action


What's this Syntax
------------------

On one hand, cool trick. On the other, we now have to figure out what ``[][counter' >= counter]_counter`` is supposed to mean.


......


It's finally time to talk about the "actions" in "Temporal Logic of Actions".

So remember how way back I said that `strings must use double quotes <string>`? That's because single quotes have a special role in TLA+! In any given step, ``x'`` is the value of x at the *end of the step*, and what it starts as in the *next* step. ``[](x' >= x)``, then, is "it is always true that the *next value of x* is larger than x".

.. tip:: you can use primed operators in the `trace explorer`. It'll show you the value of the expression in the next step.

.. index:: UNCHANGED

But that's not (yet) a valid TLA+ property. Consider the slightly different property ``[](x' = x + 1)``: "x always increases by exactly one". What happens if we insert a `stutter step <stuttering>`? Then x doesn't change at all, which means that the property is false. But by the definition of TLA+, we can *always* insert a stutter step anywhere. So this property is *trivially* false. The more interesting property we actually wanted to check was ``[](x' # x => x' + 1)``. Alternatively, we can write this as ``x' > x \/ UNCHANGED x``.

.. _box_action:

As yet more syntactic sugar, we can write ``[](x' = x + 1 \/ UNCHANGED x)`` as ``[][x' = x + 1]_x``. This is called a :dfn:`box action formula`. Box action formulas have a special role in TLA+, and TLC can only check action properties that are box action formulas.

.. todo:: more explanation?

.. tip:: The underscory bit means that we could have written the property as ``[][counter' > counter]_counter``. Expanding all the steps: 

  #. ``[counter' > counter]_counter``
  #. ``counter' > counter \/ UNCHANGED counter``
  #. ``counter' > counter \/ counter' = counter``
  #. ``counter' >= counter``

  But in general, you shouldn't rely on that aspect of ``[]_x`` for your property. If it's okay for counter to stay the same, *make that explicit*.

More Action Properties
-----------------------

Let's add another property that "the lock can't go straight from one thread to another":

.. spec

And now we'll make a change that breaks this property:

.. change


Running with ``PROPERTY LockCantBeStolen`` shows this fail.

Another way we could have writen the property:

.. todo:: Putting quantifiers inside action properties

{{ A property using ``\A`` }}

unfortunately, TLC can't check this, due to limitations of the model checker. 

| Error

What we can do in this case is pull the quantifier *inside* the action property.

.. example

.. todo:: 

  {CONTENT}
  - ENABLED
  - ``<<A>>_v``

Summary
========

- Action properties are properties on *transitions* of a system, and are checked as temporal properties.
- ``x'`` is the value of ``x`` in the *next* state. Operators with primes in them are called **Actions**.
- ``[P]_x`` means that ``P /\ UNCHANGED x``. If 
