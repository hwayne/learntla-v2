.. _core:

#########
Core
#########

This is the core language material. You can think of this section as a self-contained "book" that gets you from a complete outsider to a beginning practitioner. People who are already comfortable with TLA+ may find the :doc:`topics </topics/index>` more useful.

.. who this is for
.. who this is not for

Outline
========

As a *very* rough guide, here's the order we'll learn things: 

- How to do basic operations, like adding two numbers or concatting two sequences.
- How to specify simple, deterministic, nonconcurrent algorithms, like "check if this list has any duplicates in it", and how to check if invariants hold.
- Specifying *nondeterministic* algorithms, like ones involving randomness or a chance of failure.
- Specifying concurrent systems, like independent readers and writers sharing a queue.
- Specifying *temporal properties*, or properties on the entire lifetime on the system, like "eventually all servers come online".
- Everything else.

Everything up to and including "temporal properties" is necessary to fully use TLA+. Everything after that adds further power.

Notes on the Material
=====================

Examples
--------

Right now the guide is pretty light on examples. More interesting examples are in the :doc:`examples </examples/index>` section.

.. note:: I haven't put in many examples yet, though I have links to ones I've found around the web!

.. index:: ! pluscal

PlusCal vs TLA+
---------------

There are two languages that people write TLA+ in practice. First, you can do everything in TLA+ ("pure TLA+"). Second, you can treat it as an "assembly language" of sorts, and write most of your basic logic in TLA+ but handle all the state transitions in a DSL. There's an official DSL for this called "PlusCal", which is what we'll be starting with. I prefer doing things this way for two reasons:

1. Specification is an extremely dense, interconnected topic. By teaching PlusCal first, I can teach *some* aspects of the topic in an isolated, useful way, and gradually introduce other on top of that. This is called `scaffolding`. By contrast, if you learn pure TLA+ first, you have to learn everything all at once to get anything done.
2. Once you know PlusCal, it is *extremely* easy to learn pure TLA+. I'll be able to cover all of the "new stuff" in :doc:`a single chapter <tla>`.

That said, not everybody finds it easier to learn this way, and that's fine. There are two TLA+-first resources available, both by the inventor of TLA+:

.. todo::

  * Specifying Systems
  * Video course




.. toctree::
  :maxdepth: 2
  :hidden:

  setup
  operators
  pluscal
  invariants
  constants
  functions
  nondeterminism
  concurrency
  temporal-logic
  advanced-operators
  action-properties
  tla
  modules

.. next steps
