.. todo:: 
  https://sphinx-tabs.readthedocs.io/en/latest/

.. todo:: banner saying this is under construction, see :doc:`whatsnew`

Welcome to learntla's documentation!
====================================

Most software flaws come from one of two places. A code bug is when the code doesn't match our design— for example, an off-by-one error, or a null derefence. We have lots of techniques for finding code bugs. But what about design flaws? When it comes to bugs in our designs, the best most of us are taught is "think about it really hard".

TLA+ is a language for design systems that lets you directly test those designs. Think of it like making an outline of what you want to build, and then finding erros in the outline.  and then directly test those designs. 

About this guide
----------------

This is a free online resource for learning TLA+. To help both beginners and experienced users, the guide is divided into three parts:

- The *core*: a linear introduction to all of the TLA+ language. It starts with basic operators and gradually progresses all the way to advanced topics. The core is intended to be read **linearly**: people new to TLA+ should start with the conceptual overview, and then work forward from there. People comfortable with TLA+ should skim until they find the new material.

- *Topics*: "Optional" advanced material. Any individual lesson will be useful to *many* but not *all* TLA+ users. Unlike the core, these are designed to be mostly independent of each other. If topics have dependencies on other topics, I will call them out.

- *Examples:* Applications of TLA+ to specs, showing both how to write and undersstand specs. 

The guide is still under development, check :doc:`whatsnew` to see most recent updates and the {{roadmap}} to see what I'm currently working on.


About me
--------

.. todo::

  I'm Hillel. I created a `previous version <old.learntla.com>`__ of *Learn TLA+* and am the author of the book `Practical TLA+ <PT>`_. I wrote this because I was unsatisfied with the previous version of the website and didn't like how seeing the best resource on TLA+ wasn't free. I have a blog, a twitter, and a weekly newsletter. 

.. todo:: TLA+ vs pluscal page with prerequisites

.. toctree::
   :maxdepth: 2
   :caption: Learn
   :hidden:

   intro/conceptual-overview.rst
   beginner/index
   topics/index

.. toctree::
   :maxdepth: 2
   :caption: Apply
   :hidden:

   examples/index
   
:ref:`genindex`

.. todolist::

.. todo:: == vs =
  

.. _PT: https://www.amazon.com/Practical-TLA-Planning-Driven-Development/dp/1484238281
