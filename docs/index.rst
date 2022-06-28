.. todo:: 
  https://sphinx-tabs.readthedocs.io/en/latest/

  Separate workbook for MONEYZ

  Terms

  Debug your designs

.. note::

  Welcome to Learn TLA+! This is still a work in progress, please see :doc:`whatsnew` for updates and please raise any questions or concerns at the `github repo <https://github.com/hwayne/learntla-v2>`__. I'd love to hear your feedback!

  (In the meantime, you can find the old version at `old.learntla.com <https://old.learntla.com>`__.)

Learn TLA+ and Debug your Designs
====================================

Most software flaws come from one of two places. A code bug is when the code doesn't match our design— for example, an off-by-one error, or a null dereference. We have lots of techniques for finding code bugs. But what about design flaws? When it comes to bugs in our designs, we're just taught to "think about it really hard".

TLA+ is a "formal specification language", a means of designing systems that lets you directly test those designs. Developed by the Turing award-winner Leslie Lamport, TLA+ has been endorsed by companies like AWS, Microsoft, and Crowdstrike. Think of it like making an outline of what you want to build and then finding errors in the outline itself. 

TLA+ doesn't replace our engineering skill but *augments* it. With TLA+ we can design systems faster and more confidently. When I first discovered it, it saved my company weeks of work and hundreds of thousands of dollars annually. Since then, I've wanted to make it as accessible as possible to as many people as possible. 

.. todo:: Better intro

About this guide
----------------

This is a free online resource for learning TLA+. To help both beginners and experienced users, the guide is divided into three parts:

- The *Core*: a linear introduction to all of the TLA+ language. It starts with basic operators and gradually progresses all the way to advanced topics. The core is intended to be read **linearly**: people new to TLA+ should start with the conceptual overview and then work forward from there. People comfortable with TLA+ should skim until they find new material.

- *Topics*: "Optional" advanced material. Any individual lesson will be useful to *many* but not *all* TLA+ users. Unlike the core, these are designed to be mostly independent of each other. If topics have dependencies on other topics, I will call them out.

- *Examples:* Applications of TLA+ to specs, showing both how to write and understand specs. 

.. todo:: Rethink when things have settled down: structure apparent to reader in sidebar is "Learn", "Examples" and "Reference", where "Core" and "Topics" are under "Learn" today.

This guide is still under development, check :doc:`whatsnew` to see most recent updates and the `roadmap <roadmap>` to see what I'm currently working on.


About Me
--------

I'm Hillel. I'm part of the TLA+ foundation and the author of the book `Practical TLA+`_. I wrote this because I want TLA+ to be as accessible as possible and didn't like that my book cost money. I have a `blog`_, a `twitter`_, and a `weekly newsletter`_.

.. I also maintain the `Alloy documentation <https://alloy.readthedocs.io/en/latest/>`__ and have a strong interest in `software history <https://www.hillelwayne.com/post/linked-lists/>`__, `software engineering culture <https://www.hillelwayne.com/post/are-we-really-engineers/>`__

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
   core/index
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

.. todo:: TLA+ compared to other formal methods

.. todolist::


.. _Practical TLA+: https://www.amazon.com/Practical-TLA-Planning-Driven-Development/dp/1484238281

.. _blog: https://www.hillelwayne.com
.. _twitter: https://twitter.com/hillelogram/
.. _weekly newsletter: https://buttondown.email/hillelwayne/ 
