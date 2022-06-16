.. _topic_aux_vars:

#####################
Auxiliary Variables
#####################

History, helper, prophecy, error trace varialbes

While TLA+ properties have al oto f flexibility, they also have limits. You can't "forget" a property, like say "P is true until Q is true, after while P can be false." Say you write it as "~P => Q". Then if we set ~P and *then* set ~Q, the invariant fails, even though we should have "forgotten" it. 

We can sort of fix this by adding a new variable ``Q_was_true``, then write the property as

::
  
  Prop == P => Q \/ Q_was_true

  Next ==
    /\ \* regular spec
    /\ IF Q' THEN Q_was_true' ELSE UNCHANGED Q_was_true

``Q_was_true`` is called an :index:`auxiliary variable`, or "aux var" for short. By augmenting specs with aux vars we can represent a wider range of systems and check a wider range of properties. It's not the most elegant solution, but it gets the job done.

.. note:: In other formal methods disciplines, auxiliary variables are sometimes called "ghost" or "helper" variables.

Types of Auxiliary Variables
=============================

History Variables
-----------------

Variables that represent something that happened. ``Q_was_true`` is a history variable. If you want to confirm that your history variables don't change once they're set, you can make that an `action property <action_properties>`:

::

  Prop ==
    [][Q_was_true => UNCHANGED Q_was_true]_Q_was_true

You can also use history variables to track past information no longer present in the system. Say you want to make sure that two threads alternate in the critical section, so that neither reaches the critical section twice in a row.

.. todo:: Pull the example from Dekker

Trace Variables
----------------


.. seealso::

  Aliasing

Bounding Variables
---------------------

Usage Notes
===============

Don't make the code use them
Aux vars are tricky to use in raw TLA+, as they need to be included in ``UNCHANGED`` statements.  You can use sequences to help with this. 



