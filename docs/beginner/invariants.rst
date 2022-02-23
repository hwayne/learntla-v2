.. _writing-invariant:

++++++++++++++++++++++++
Writing an Invariant
++++++++++++++++++++++++

This section covers:

* How to write invariants
* Type Invariants

* Quantifiers

* Implication


* CHOOSE?

The Golden Rule
======================

In the last section, we wrote a simple specification for finding duplicates in a sequence. It tells us if there are mistakes, but it's also a bad spec. To tell whether a spec had an issue, we did something clever.

.. note:: The golden rule of TLA+

  **Do not be clever.** Express things exactly as what they mean.

Programming teaches us to be clever. Specification is not clever.

There's two things we're doing that are clever.

#. The if statement.
#. How we check for uniqueness. Carindality? Len? Ewww.

.. note:: No, this isn't *all* the way to being not clever. We have this extra ``done`` variable we don't need. We call this an `auxiliary variable <aux-var>`: something that isn't part of the system but is for bookkeeping the spec. Sometimes aux vars are a necessary evil. But in this case, we'll later learn two separate tools to specify the property more directly: `pc` and the `eventually` operator. 


.. _invariants:

Invariants
=============



.. _type invariants:

.. technique:: Type Invariants

  TODO

Fixing the if
-----------------

.. _implication-2:

The power of ``=>``
---------------------

Quantifiers
=================


Fixing Unique
------------------

.. _implication-3:

The even more power of ``=>``
-----------------------------------

Pulling it all together
=========================
