.. todo:: 
  https://sphinx-tabs.readthedocs.io/en/latest/

  Separate workbook for MONEYZ

  Terms

  Debug your designs

.. note::

  Welcome to Learn TLA+! This is still a work in progress, please see :doc:`whatsnew` for updates and please raise any questions or concerns at the `github repo <https://github.com/hwayne/learntla-v2>`__.

  (In the meantime, you can find the old version at `old.learntla.com <https://old.learntla.com>`__.)

Learn TLA+
====================================

Most software flaws come from one of two places. A code bug is when the code doesn't match our design— for example, an off-by-one error, or a null derefence. We have lots of techniques for finding code bugs. But what about design flaws? When it comes to bugs in our designs, the best most of us are taught is "think about it really hard".

TLA+ is a language for design systems that lets you directly test those designs. Think of it like making an outline of what you want to build, and then finding erros in the outline.  and then directly test those designs. 

`genindex`

About this guide
----------------

This is a free online resource for learning TLA+. To help both beginners and experienced users, the guide is divided into three parts:

- The *core*: a linear introduction to all of the TLA+ language. It starts with basic operators and gradually progresses all the way to advanced topics. The core is intended to be read **linearly**: people new to TLA+ should start with the conceptual overview, and then work forward from there. People comfortable with TLA+ should skim until they find the new material.

- *Topics*: "Optional" advanced material. Any individual lesson will be useful to *many* but not *all* TLA+ users. Unlike the core, these are designed to be mostly independent of each other. If topics have dependencies on other topics, I will call them out.

- *Examples:* Applications of TLA+ to specs, showing both how to write and understand specs. 

The guide is still under development, check :doc:`whatsnew` to see most recent updates and the `roadmap <roadmap>` to see what I'm currently working on.


About me
--------

I'm Hillel. I created a `previous version <old.learntla.com>`__ of *Learn TLA+* and am the author of the book `Practical TLA+`_. I wrote this because I was unsatisfied with the previous version of the website and didn't like how seeing the best resource on TLA+ wasn't free. I have a `blog`_, a `twitter`_, and a `weekly newsletter`_. 

.. todo:: TLA+ vs pluscal page with prerequisites

.. toctree::
  :maxdepth: 2
  :hidden:

  Intro <self>
  whatsnew

.. toctree::
   :maxdepth: 2
   :caption: Learn
   :hidden:

   intro/conceptual-overview.rst
   beginner/index
   topics/index

.. toctree::
   :maxdepth: 3
   :caption: Examples
   :hidden:

   examples/index

.. toctree::
  :caption: Reference
  :hidden:

  reference/glossary
  reference/other-resources

.. todo:: https://stackoverflow.com/questions/25243482/how-to-add-sphinx-generated-index-to-the-sidebar-when-using-read-the-docs-theme
   

.. todolist::

.. todo:: == vs =
  

.. _Practical TLA+: https://www.amazon.com/Practical-TLA-Planning-Driven-Development/dp/1484238281

.. _blog: https://www.hillelwayne.com
.. _twitter: https://twitter.com/hillelogram/
.. _weekly newsletter: https://buttondown.email/hillelwayne/ 
