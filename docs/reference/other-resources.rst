.. _other_resources:

++++++++++++++++++++++
Other Resources
++++++++++++++++++++++

Learning Resources
==================

`Specifying Systems`_
  This is a comprehensive introduction and formal grounding of TLA+, though it has very little on model checking. Does not cover features past 2004 or so (like PlusCal and `recursive`).

`TLA+ Video Course`_
  A video course by the inventor of TLA+.

.. https://apalache-mc.org/docs/idiomatic/index.html

`Introduction to Formal Pragmatic Modeling <https://elliotswart.github.io/pragmaticformalmodeling/>`__
  A fantastic dive into three large production-level specifications. Assumes some TLA+ knowledge.

Reference Material
-------------------

`TLA+ Language Reference Manual <https://apalache-mc.org/docs/lang/index.html>`__
  A formal reference by the developers of `Apalache <apalache>`. Work in progress.

`TLA+ Version 2 <https://lamport.azurewebsites.net/tla/tla2-guide.pdf>`__
  Covers `recursive` and lambda expressions.

`Current Versions of the TLA+ Tools <https://lamport.azurewebsites.net/tla/current-tools.pdf>`__
  Information on TLC flags if you run it from the `command line <topic_cli>`, as well as the other tools (except PlusCal). Information on TLC module operators.

`Pluscal Manual <https://lamport.azurewebsites.net/tla/p-manual.pdf>`__
  Formal definition of PlusCal, flags, and command line options. See f.ex the "label" option on page 70, which automatically generates the labels your spec needs.
  
`Summary of TLA+ <https://lamport.azurewebsites.net/tla/summary-standalone.pdf>`__
  A TLA+ cheat sheet. Includes some TLA+ constructs that none of the tooling can check, like action composition. Uses typeset symbols instead of ASCII ones (so :math:`\in` instead of ``\in``).

Reading Resources
=================

`How Amazon Web Services uses Formal Methods  <https://cacm.acm.org/magazines/2015/4/184701-how-amazon-web-services-uses-formal-methods/fulltext>`__
  The paper that first got major companies interested in using TLA+. Also how I found out about it.

`TLA+ Example Repository <https://github.com/tlaplus/Examples>`__
  A collection of abstract algorithms and protocols.

`TLA+ in Practice and Theory <https://pron.github.io/tlaplus>`__
  A detailed analysis of the mathematical theory that underpins TLA+.

`Let's Prove Leftpad <https://github.com/hwayne/lets-prove-leftpad>`__
  A collection of proofs of leftpad in different formal methods. Not entirely related to TLA+ but <shameless plug here>


Talks
=====

`Designing Distributed Systems with TLA+ <https://www.hillelwayne.com/talks/distributed-systems-tlaplus/>`__
  My standard pitch talk for using TLA+.

`Weeks of Debugging can save you Hours of TLA+ <https://www.youtube.com/watch?v=wjsI0lTSjIo>`__
  Markus (the core toolbox developer)'s pitch talk for using TLA+.

Other Tooling
==============

`TLA+ Community Modules <https://github.com/tlaplus/CommunityModules>`__
  A collection of useful modules to add to the minimal TLA+ stnadard library.

.. _apalache:

`Apalache <https://apalache-mc.org/>`__
  An alternate model checker for TLA+. It uses symbolic model checking instead of enumerating all states. 

  (Disclosure, I'm currently doing some consulting work for Informal Systems.)

.. _tlaps:

`TLAPS <https://tla.msr-inria.inria.fr/tlaps/content/Documentation/Tutorial/The_example.html>`__: A proof system for TLA+ if you want to use it as a :term:`theorem prover`.

`VSCode plugin <https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus>`__
  For if you want to run TLA+ outside of the toolbox, but not in the command line.

`TLA2JSON <https://github.com/japgolly/tla2json>`__
  Does exactly what it says it does. There's plans to add this feature to the toolbox, but that isn't ready yet.

`tree-sitter-tlaplus <https://github.com/tlaplus-community/tree-sitter-tlaplus>`__
  The `Treesitter <https://tree-sitter.github.io/tree-sitter/>`__ parser-generator.


Community
==========

`The TLA+ Homepage <https://lamport.azurewebsites.net/tla/tla.html>`__

`conf.tlapl.us <http://conf.tlapl.us/home/>`__
  The standard site where we put info on our annual TLA+ conference. Usually cohosted with `Strange Loop <https://www.thestrangeloop.com/>`__.

`TLA+ Google Group <https://groups.google.com/g/tlaplus>`__
  This is where all the core developers hang out and answer people's questions.

`r/tlaplus <https://www.reddit.com/r/tlaplus/>`__
  The TLA+ subreddit.

.. _Specifying Systems: https://lamport.azurewebsites.net/tla/book.html
.. _TLA+ Video Course: https://lamport.azurewebsites.net/video/videos.html
