.. _topic_cli:

########################
Beyond the Toolbox
########################

Most people use the Toolbox for TLA+. But you can also use `vscode <https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus>`_ or the command line. 

The Command Line
=================

The main CLI file is ``tla2tools.jar``. You can download it directly from `this link <https://github.com/tlaplus/tlaplus/releases>`_. You can also find it in the base directory of your toolbox installation.

Tlatools has four subtools: TLC, the pluscal translator, a latex pdf generator (Tla2Tex), and a parser (SANY). I'll leave documenting the latter two tools to `Lamport <https://lamport.azurewebsites.net/tla/current-tools.pdf>`_ and focus on the translator and model checker.

The Pluscal Translator
------------------------

To translate a PlusCal algorithm in a file, write

.. code-block:: bash

  $ java -cp tla2tools.jar pcal.trans file.tla

This will:

1. Translate the text *in file* to TLA+
2. Write ``file.old`` as a backup
3. Write ``file.cfg`` as a :ref:`configuration file <cfg>`, overwriting it if it already exists.

To prevent (3), add ``-nocfg`` as a flag before ``file.tla``. There is no way to prevent the translator from writing ``file.old``. I have a shell watcher that finds and deletes them.

You can read about all of the other translator options `here <https://lamport.azurewebsites.net/tla/p-manual.pdf>`__, page 67-69, or by running ``java -cp tla2tools.jar pcal.trans -h``.

TLC
-------

To run TLC on a model, write:

.. code-block:: bash

  $ java -jar tla2tools.jar -config configfile.cfg specfile.tla

If ``-config`` isn't provided, TLC will by default look for ``specfile.cfg``. This is the file that holds all of the configuration options for the model run.

TLC has other flags, but if you can't write a config format that's all moot, so let's talk about that.

.. _cfg:

Config Format
.............

The model checking config language is a special DSL for using TLC from the command line. It's what the toolbox abstracts away on the backend.

All config files need a ``SPECIFICATION {spec}`` line, where ``Spec`` is whatever action encompasses your initial and next states. By convention, this should be called ``Spec``, but this isn't required— useful if you want different configs to test different variations of your system.

Invariants you want to check must be prefixed with ``INVARIANT``, temporal properties with ``PROPERTY``. Both can have commas, eg ``INVARIANT TypeInvariant, IsSafe`` is a valid line. Unlike in the toolbox, you **cannot** make expressions invariants— they must be named operators.

.. note:: Why does that work in the toolbox? When you make an expression an invariant, the Toolbox makes a separate ``MC.tla`` file, adds that expression as an operator, and then model checks ``MC.tla`` with the new operator as an invariant. It does a similar thing to get around restrictions on constant expressions, below.

Constants are written as ``CONSTANT name = value``. Values can be simple values or sets of simple values, but not functions or expressions. To set a model value instead of an ordinary assignment, write ``CONSTANT name = name`` instead. To make a set of model values, write ``name = {a, b, c}``, where ``a, b, c`` are identifiers (**not** strings). 

.. warning:: Since the config files can't use imports and negative numbers are *technically an Integers import*, you can't set a negative number as a constant.

A basic config file might look like this:

.. code-block::

  SPECIFICATION Spec

  INVARIANT Inv1, Inv2
  PROPERTY Prop1

  CONSTANT 
    Const1 = {"a", "b", "c"}
    Const2 = Const2
    Const3 = {c1, c2, c3}


Config files may also have ``CONSTRAINT``, ``ACTION-CONSTRAINT``, ``VIEW``, which work equivalently to their `Toolbox options <topic_toolbox>`.  You can also disable deadlock checking in the cfg with ``CHECK_DEADLOCK FALSE``.

.. index: ALIAS
.. _ALIAS:

Finally, we have ``ALIAS``. This lets us effectively simulate the `Error Trace Explorer <trace_explorer>` on the command line. Let's say we have the following spec:

::

  ---- MODULE aliases ----
  EXTENDS Integers

  VARIABLE x
  Init == 
    x = 0

  Next == x' = x + 1
  Inv == x < 10
  Spec == Init /\ [][Next]_x

  Alias ==
    [x |-> x,
     nextx |-> x',
     incx |-> x + 1]
  =====

If we add ``ALIAS Alias`` to our config file, then the error trace will show the values of x, ``nextx``, and ``incx`` in the error output.

.. note:: The alias *replaces* the standard error output. If you don't include some variables in the alias, then they won't show on the error output either.

.. todo:: Symmetry sets


.. _tlc_options:

TLC Options
-----------

Now that we know how to run a config file, let's get back to the TLC options. You can read all of them with ``java -jar tla2tools.jar -help`` (*not* ``-h``), or by reading them `here <https://lamport.azurewebsites.net/tla/current-tools.pdf>`_ (pages 9-11). Most of them are self-explanatory or equivalent to toolbox options. See the `Toolbox topic <topic_toolbox>` for more information on how to use them. The main things of note are:

``-continue``
  Will continue model checking even after a violation is found. Every single invariant violation will be dumped as output.

  .. warning::

    Don't pass this in `as a flag in the toolbox <toolbox_tlc_cl>`, or it will think it's an error:

      | An error has occurred. See error log for more details.
      | assertion failed: Two traces are provided. Unexpected. This is a bug

.. _dump:

``-dump file``
  Writes all of the states that TLC reached to ``file`` *in no particular order*. If you want to know how the states *connect* to each other, instead write

``-dump dot file``
  This outputs a `graphviz <https://graphviz.org/>`_ graph file instead. Nodes are states, labelled with their variable assignments. TLC will *not* append the file extension to the filename; you'll have to add that yourself.

  .. note:: If your spec includes a liveness property, TLC will also write ``file_liveness``. This is an internal representation and `can be ignored <https://groups.google.com/g/tlaplus/c/olBAjD-9btA>`_.

  You can also write ``-dump dot,colorize file`` to color the edges based on the actions they involve and ``-dump dot,actionlabels`` to label the edges with the corresponding action. Both can be used together.

``-metadir dir``
  Instead of storing the seen statespace in the same directory as the spec, TLC will instead store it in ``dir``. I find this useful when scripting against the CLI, as I can store the state space in a temporary directory for easier cleanup.

``-workers num/auto``
  Specifies the number of worker threads to use for model checking. **This is very important.** Without this, the CLI defaults to a single worker. Pass in ``auto`` to use as many workers as you have cores.

``-noGenerateSpecTE``
  Newer versions of TLA+ save an error file whenever it finds a property error. This flag disables writing the file.

``-fpmem num``
  What percentage of the system memory to earmark for model checking, expressed as a decimal. Defaults to ``0.25`` (1/4 the memory).
