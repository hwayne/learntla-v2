.. learntla documentation master file, created by
   sphinx-quickstart on Thu Jan 27 12:28:32 2022.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

.. todo:: 
  https://sphinx-tabs.readthedocs.io/en/latest/

.. todo:: IsUnique(<<x, y, z>>)

Welcome to learntla's documentation!
====================================

Most software flaws come from one of two places. A code bug is when the code doesn't match our design— for example, an off-by-one error, or a null derefence. We have lots of techniques for finding code bugs. But what about design flaws? We can't find issues in our designs. TK

TLA+ is a language for design systems that lets you directly test those designs. Think of it like making an outline of what you want to build, and then finding erros in the outline.  and then directly test those designs. 

About this guide
----------------

This is a free online resource for learning TLA+ . The guide is divided into three parts:

* The *core*: 
About me
--------

Blah blah
expectations, it could be that the code is wrong. Most software correctness techniques –
types, tests, etc. – are used to check the code. But it could instead be that the code is
correct and our expectations are wrong: there’s a fundamental error in our design.
These errors, called specification errors, are some of the most subtle and dangerous
bugs. They can span multiple independent programs, occur in convoluted race
conditions, or depend on physical phenomena. Our regular tools simply can’t find them.
Instead, we can find them with a specification language such as TLA+. TLA+ is
the invention of Leslie Lamport, winner of the 2013 Turing Award and the inventor of
Paxos and LaTeX. Instead of writing your design in code or plain English, you write it
in TLA+’s special notation. Once you specify your core assumptions and requirements,
it can explore how that system would evolve over time, and whether it actually has the
properties you want.
How to read this book

.. toctree::
   :maxdepth: 2
   :caption: Learning
   :hidden:

   intro/conceptual-overview.rst
   beginner/index
   intermediate/index
   
:ref:`genindex`

.. todolist::


.. applying



