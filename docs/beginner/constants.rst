.. _chapter_constants:

###############
Constants
###############

- CONSTANTs
- ASSUME
- Model Values
- Instances?


.. index:: constants, CONSTANT
  :name: constant

CONSTANT
========

Okay, *actual* last time we touch our duplicate checker.
Getting back to our duplicate checker— actually you know what I'm sick of that damn thing. Our new best friend is the `threads` spec. Here's where we left off:

TK

If I want to test it with two threads, I set ``NumThreads == 2``. If I want to test it with six threads, I set ``NumThreads == 6``.

Now the more threads we have, the bigger the state space and the longer the spec will take to run. If I was hacking on the spec a lot, I'd want to do most of my iteration with two threads and catch bugs early that way. Once that's working, I'd then kick it up to six threads and make sure that's also correct. But then which version do I share with my coworkers, ``NumThreads == 2`` or ``NumThreads == 6``?

Environmental variables
Answer: neither. It doesn't make sense to fix the number of threads *in the definition of the spec*. We should instead define the spec to work for an arbitrary number of threads, and then pick the actual number at model-checking time.

We specify, then, that ``NumThreads`` is a **constant**: something where the value is picked outside the TLA+. [#footnote-constant]_


.. def constant


Now, in the "Model Overview" page of the toolbox, ``NumThreads`` appears as something to assign. We can give it a different value in each model. If we give it an ordindary assignment of ``6``, then it'll be like we wrote ``NumThreads == 6`` in the spec.

.. todo:: image

.. index:: ASSUME
  :name: ASSUME

ASSUME
-------

::

  NumThreads <- 0

Model doesn't start if the assumption is wrong

::

  ASSUME NumThreads > 0

.. index:: Model Values
  :name: model_values

Model Values
----------------

Sentinel value

Model values

Compare false to everything BUT themselves, don't raise an error

replace the sentinel value in ``threads``

.. index::
  :pair: Model values, sets of
  :name: model_set


Symmetry sets?

Something else
===================

Okay this chapter is a little on the short side, let's throw in one more thing.


Summary
===========

.. [#footnote-constant] This is different from how we use constant in programming languages, as well as other specification languages. AFAICT it's an idiosyncracy of TLA+. Constants as in "values that never change" are just 0-arity operators.
