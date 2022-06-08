.. _topic_tips:

############
General Tips
############

General small things for writing specs better. Broken into

Both

Pluscal

TLA+

Both
===========

Use LET, ASSUME

Decouple variables

Use shell scripts
THEOREM

Typeinvariants, stateconstraints

.. Latchkeys and tripwires 

  Maybe that's it's own topic

Pluscal
===========

Abuse macros
While loops considered harmful
State sweeping
Duplicate processes

TLA+
===========

Conjoining in
Bottom-level your actions

Helper Actions
@

Parameterize your actions
-------------------------

Instead of

::

  Add ==
    \E w \in Worker: s' = s \union {w}

  Remove ==
    \E w \in Worker: s' = s \ {w}

  Next == Add \/ Remove

Do

::

  Add(w) == s' = s \union {w}
  Remove(w) == s' = s \ {w}

  Next ==
    \E w \in Worker:
      \/ Add(w) 
      \/ Remove(w)
