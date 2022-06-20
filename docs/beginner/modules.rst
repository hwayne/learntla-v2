.. _chapter_modules:

########
Modules
########

I'm covering Modules last because they're not as important for organizing specs  as they are for organizing code. Most specs are under 300ish lines so you can keep them all in one file with little trouble.

{{That said, sometimes you want to create an abstract library like ``Sequences``, and sometimes you want to refine something, which is a really complex topic we'll cover in topics, not the core. Also, some people like putting their invariants in a separate file. So here's how to modularize your spec.}}

Modules
=========

Shared TLA+ files should be in the same folder as your spec.

The toolbox has a config option TK for reaching a shared directory.

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
  :name: INSTANCE

INSTANCE
==========

This deserves a bigger section, because ``INSTANCE`` is way more interesting than ``EXTENDS``. If you write

::

  INSTANCE Sequences

Then ``Sequences`` is dumped into the file namespace, just like before. So why would you want to use it? There's a couple minor differences between ``INSTANCE`` and ``EXTENDS``:

1. You can have more than one ``INSTANCE`` in a spec, while you can only have one ``EXTENDS``.
2. You can import an instance "locally" with ``LOCAL INSTANCE``. Then the imported module is available, but imported operators won't be transitively included another spec.

  (You can see this used in ``Sequences.tla``, which locally imports Naturals.)

And there's also a couple of major differences.

Namespacing
------------

As anybody who's worked with Python or C++ or anything that allows unqualified imports knows, you really don't want to dump everything into the file namespace. That gets everybody mad!

You can namespace the operators in an instance like this:

::

  Foo == INSTANCE Sequences

Namespace lookup is done with ``!``. So instead of writing ``Append(seq, 1)``, you'd write ``Foo!Append(seq, 1)``.

.. tip::

  Yes, you can in fact import a module in the middle of a `LET`.

  ::

    LET Foo == INSTANCE Sequences
    IN Foo!Append(seq, 1)

In fact you can import the same module multiple times under different names:

::

  Foo == INSTANCE Sequences
  Bar == INSTANCE Sequences

Why would you want to do that? Well, it wouldn't be useful with the standard library functions, but if your imported module has some constants... well, that's where things get interesting.

.. index::
  single: INSTANCE; Parameterizing Modules

Parameterized Modules
======================

{{Use parameterization when the module you're importing has constants and variables}}

.. index:: WITH
.. _WITH:

::
  
  Foo == INSTANCE TK WITH X <- Y

.. tip:: If the importing module has a constant with the same name as the child model, it will be imported by default. For example, if both modules contain a ``DEBUG`` constant, the following two are equivalent:

  ::

    M == INSTANCE Module WITH DEBUG <- DEBUG
    M == INSTANCE Module

  (You can still provide your own value in the ``WITH`` as an override.)

Parameterized Variables
------------------------

If you parameterize a module over a variable, you can use actions in that model as regular actions. For example:

TK

Partial Parameterization
------------------------

.. seealso::
  
  Test
    Bar

Using Modules
===================

* Breaking things up
* Shared Libraries
* Refinement
