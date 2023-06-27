.. _examples:

.. note:: There aren't a whole lot of examples uploaded yet. I'll be writing more as I continue to work on the site. In the meantime, here are some good examples from around the web!

  * `TLA+ Example Repository <https://github.com/tlaplus/Examples>`__: The official repo, mostly abstract algorithms and protocols.

  * `Modeling a message passing bug with TLA <https://medium.com/@polyglot_factotum/modelling-a-message-passing-bug-with-tla-baaf090a688d>`__

  * `The Tortoise and Hare in TLA+ <https://surfingcomplexity.blog/2017/10/16/the-tortoise-and-the-hare-in-tla/>`__: That finding cycles in a linked list algorithm question, formally modeled.

  * `Message Queues <https://www.hillelwayne.com/post/tla-messages/>`__: Pubsub implementations with topics readers subscribe to.

  * `Thread Bounded Queue <https://www.hillelwayne.com/post/augmenting-agile/>`__: finding a deadlock in a bounded queue, where writers trying to write a full queue are temporarily put to sleep.

  * `Adversarial Modeling <https://www.hillelwayne.com/post/adversaries/>`__: A short example of splitting a spec into "machine" and "world" components, where the world acts as an adversary against the machine.
  
  * `Xen VChan <http://roscidus.com/blog/blog/2019/01/01/using-tla-plus-to-understand-xen-vchan/>`__

  * `Batch uploader <https://medium.com/espark-engineering-blog/formal-methods-in-practice-8f20d72bce4f>`__: The first spec I wrote in production!

  * `Process Handler <https://andy.hammerhartes.de/finding-bugs-in-systems-through-formalization.html>`__

  * `Payment Handler <https://www.g9labs.com/2022/03/12/what-s-the-fuss-about-formal-specifications-part-2/>`__: Like the wire example in the conceptual overview, except in real life.

  * `Raft consensus algorithm <https://github.com/ongardie/raft.tla>`__

  See also `Introduction to Formal Pragmatic Modeling <https://elliotswart.github.io/pragmaticformalmodeling/>`__, which is an in-depth discussion of three large production-level specifications.



+++++++++
Operators
+++++++++


.. toctree::
  :titlesonly:

  partitions


.. Graph library
  Transitive tree selection
  Inverting a function of sets, and what happens if the something doesn't have an element (show this with function sets)


+++++++++++++
PlusCal Specs
+++++++++++++


.. toctree::
  :titlesonly:

  golang

..
  - Algorithms (binary search, topological sort)
  - XP14
  - Dining philosophers from old learntla
  


  Ideas:

    - Mutex DAG tracer?

.. todo::
  - ksubsets operator
  - Task ordering
  - https://tavianator.com/2023/futex.html
