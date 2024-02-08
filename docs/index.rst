.. todo:: 
  https://sphinx-tabs.readthedocs.io/en/latest/

  Separate workbook for MONEYZ

  Use https://github.com/sphinx-toolbox/sphinx-toolbox/blob/master/sphinx_toolbox/assets.py for downloads

  Make a role so I can write ``:r:`thing``` for ```thing <thing>```

  Use the .. sidebar directive!

  Add an "external resources" section"

.. note::

  Welcome to Learn TLA+! This is still a work in progress, please see :doc:`whatsnew` for updates and please raise any questions or concerns at the `github repo <https://github.com/hwayne/learntla-v2>`__. I'd love to hear your feedback!

  (In the meantime, you can find the old version at `old.learntla.com <https://old.learntla.com>`__.)

Learn TLA+
====================================

Most software flaws come from one of two places. A code bug is when the code doesn't match our design— for example, an off-by-one error, or a null dereference. We have lots of techniques for finding code bugs. But what about design flaws? When it comes to bugs in our designs, we're just taught to "think about it really hard".

TLA+ is a "formal specification language", a means of designing systems that lets you directly test those designs. Developed by the Turing award-winner Leslie Lamport, TLA+ has been endorsed by companies like AWS, Microsoft, and CrowdStrike. TLA+ doesn't replace our engineering skill but *augments* it. With TLA+ we can design systems faster and more confidently. Check out the `chapter_overview` to see an example of this in practice.

About this guide
----------------

This is a free online resource for learning TLA+. To help both beginners and experienced users, the guide is divided into three parts:

- The |core|: a linear introduction to all of the TLA+ language. It starts with basic operators and gradually progresses all the way to advanced topics. The core is intended to be read **linearly**: people new to TLA+ should start with the conceptual overview and then work forward from there. People comfortable with TLA+ should skim until they find new material.

- |topics|: "Optional" advanced material. Any individual lesson will be useful to *many* but not *all* TLA+ users. Unlike the core, these are designed to be mostly independent of each other. If topics have dependencies on other topics, I will call them out.

- |examples|: Applications of TLA+ to specs, showing both how to write and understand specs. 

This guide is still under development, check :doc:`whatsnew` to see most recent updates and the `roadmap <roadmap>` to see what I'm currently working on.


About Me
--------

I'm Hillel. I'm part of the TLA+ foundation and the author of the book `Practical TLA+`_. I wrote this because I want TLA+ to be as accessible as possible and didn't like that my book cost money. I have a `blog`_ and a `weekly newsletter`_.

(Full disclosure, I'm also a `professional  TLA+ consultant <https://hillelwayne.com/consulting/>`__ and <plug>run workshops</plug>.)

.. I also maintain the `Alloy documentation <https://alloy.readthedocs.io/en/latest/>`__ and have a strong interest in `software history <https://www.hillelwayne.com/post/linked-lists/>`__, `software engineering culture <https://www.hillelwayne.com/post/are-we-really-engineers/>`__

.. toctree::
  :maxdepth: 2
  :hidden:

  Intro <self>
  intro/faq
  whatsnew
  intro/conceptual-overview.rst

.. toctree::
  :hidden:
  :maxdepth: 3
  :caption: TLA+

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
  reference/standard-library
  reference/other-resources

.. While `index` looks like it's under the Reference toctree, it's actually injected as part of a template (_templates/globaltoc.html)

.. _Practical TLA+: https://www.amazon.com/Practical-TLA-Planning-Driven-Development/dp/1484238281

.. _blog: https://www.hillelwayne.com
.. _weekly newsletter: https://buttondown.email/hillelwayne/ 


.. http://carefully.understood.systems/blog-2017-04-19-bounded-log-queue.html

.. https://stackoverflow.com/questions/3280712/how-to-allow-certain-threads-to-have-priority-in-locking-a-mutex-use-pthreads

.. todolist:: 
