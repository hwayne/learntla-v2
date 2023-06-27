.. _chapter_modules:

########
Modules
########

I'm covering modules last because they're not as important for organizing specs  as they are for organizing code. Most specs are under 300ish lines so you can keep them all in one file with little trouble.

That said, sometimes you want to create an abstract library like ``LinkedLists``, and some people like putting their invariants in a separate file. So here's how to modularize your spec.

Modules
=========

Shared TLA+ files should be in the same folder as your spec.

.. tip:: The toolbox has a config option (TLA+ Preferences > TLA+ Library Path Functions) for reading modules from a shared directory. Any module in this directory can be used by all your specifications.

Once you have your module, how do you import it? There's a couple of ways:

.. index:: 
  single: EXTENDS
  single: LOCAL
  seealso: LOCAL; INSTANCE

EXTENDS
--------

This is what we've been using. Everything on the ``EXTENDS`` line is dumped into the same namespace as your file. If ``Sequences`` defines an ``Append`` operator, then ``EXTEND Sequences`` drops ``Append`` into your spec.

*Unless* the operator is ``LOCAL``. If you write

::

  LOCAL Op == "definition"

Then ``Op`` will not be imported when extended.

And that's all there is to say about extensions! Let's talk about the much more interesting module mechanism, instances. 

.. index:: INSTANCE
.. _INSTANCE:

INSTANCE
==========

This deserves a bigger header because ``INSTANCE`` is way more interesting than ``EXTENDS``. If you write

::

  INSTANCE Sequences

Then ``Sequences`` is dumped into the file namespace, just like before. So why would you want to use it? There's a couple minor differences between ``INSTANCE`` and ``EXTENDS``:

1. You can have more than one ``INSTANCE`` line in a spec, while all your ``EXTENDS`` have to be on the same line.
2. You can import an instance "locally" with ``LOCAL INSTANCE``. Then the imported module is available, but imported operators won't be transitively included another spec.

  (You can see this used in ``Sequences.tla``, which locally imports Naturals.)

And there's also a couple of major differences.

Namespacing
------------

As anybody who's worked with Python or C++ or anything that allows unqualified imports knows, you really don't want to dump everything into the file namespace. That gets everybody mad! You can namespace the operators in an instance like this:

::

  Foo == INSTANCE Sequences

.. index:: `!` (Namespace lookup)

Namespace lookup is done with ``!``. So instead of writing ``Append(seq, 1)``, you'd write ``Foo!Append(seq, 1)``.

.. tip::

  Yes, you can import a module in the middle of a `LET`.

  ::

    LET Foo == INSTANCE Sequences
    IN Foo!Append(seq, 1)

In fact you can import the same module multiple times under different names:

::

  Foo == INSTANCE Sequences
  Bar == INSTANCE Sequences

Why would you want to do that? Well, it wouldn't be useful with the standard library functions, but if your imported module has some constants… well, that's where things get interesting.

.. index::
  single: INSTANCE; Parameterized Modules

Parameterized Modules
----------------------

Here's a new module:

.. todo:: move into an xml

::

  ---- MODULE Point ----
  LOCAL INSTANCE Integers
  CONSTANTS X, Y
  ASSUME X \in Int /\ Y \in Int

  Repr == <<X, Y>>
  Add(x, y) == <<X + x, Y + y>>
  ====

Unlike previous modules we've seen, this one contains constants. When we import it with ``WITH``, we need to define what those constants are. We do it like this:

.. index:: 
  single: WITH
  single: <-
  single: INSTANCE; WITH

.. _with_tla:

::
  
  Origin == INSTANCE Point WITH X <- 0, Y <- 0

This effectively "rewrites" all of the operators in ``Point`` to use the passed in values. Now ``Origin!Add(x, y) == <<0 + x, 0 + y>>``.

.. tip:: If the importing module has a constant with the same name as the child model, it will be imported by default. For example, if both modules contain a ``DEBUG`` constant, the following two are equivalent:

  ::

    M == INSTANCE Module WITH DEBUG <- DEBUG
    M == INSTANCE Module

  (You can still provide your own value in the ``WITH`` as an override.)

.. todo:: 

  {content} If you parameterize a module over a variable, you can use actions in that model as regular actions. For example:

  ::

    ---- MODULE test -----

    VARIABLE x

    Inc == x' = x + 1

  This is more useful for defining constraint predicates



Partial Parameterization
------------------------

We can also write this:

::

  XAxis(X) == INSTANCE Point WITH Y <- 0

Now instead of ``XAxis!Add(x, y)``, we write ``XAxis(v)!Add(x, y)``, which defines what the ``X`` constant "should be" at runtime. eg ``XAxis(2)!Add(x, y) == <<2 + x, 0 + y>>``.

.. note:: I haven't yet converted it into a proper topic, but `this article of mine <https://hillelwayne.com/post/tla-adt/>`__ covers a set of techniques where partial parameterization is useful. 

.. todo:: {EXPAND} Using Modules

Summary
===========

- EXTENDS will not import any operators prefixed with ``LOCAL``.
- ``INSTANCE`` is like ``EXTEND``, except it can be namespaced. Namespaced operators are called with  ``I!operator``.
- You can instantiate modules with constants and pass them in at instantiation. You can also partially instantiate a module, and pass in the remaining values when calling an operator.
