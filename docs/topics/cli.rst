.. _topic_cli:

########################
Beyond the Toolbox
########################

Most people use the Toolbox for TLA+. But what if you want to run it from the command line? Or VsCode? There's an `extension` for using it from VsCode.

The Command Line
=================

The main CLI file is ``tla2tools.jar``. You can download it directly from `this link <www.example.org>`_. You can also find it in the Toolbox installation, under ``TODO PATH``.

Tlatools has four subtools: TLC, the pluscal translator, a latex pdf generator (Tla2Tex), and a parser (SANY). I'll leave documenting the latter two tools to Lamport TODO and focus on the translator and model checker.

The Pluscal Translator
------------------------

To translate a PlusCal algorithm in a file, write

.. code-block::

  $ java -cp tla2tools.jar pcal.trans file.tla

This will:

1. Translate the text *in file* to TLA+
2. Write ``file.old`` as a backup
3. Write ``file.cfg`` as a `configuration file <cfg>`, overwriting it if it already exists.

To prevent (3), add ``-nocfg`` as a flag before ``file.tla``. There is no way to prevent the translator from writing ``file.old``. I have a shell watcher that finds and deletes them.

You can read about all of the other translator options `here <pcal_manual>`_, page TODO, or by running ``java -cp tla2tools.jar pcal.trans -h``.

TLC
-------

To run TLC on a model, write:

.. code-block::

  $ java -jar tla2tools.jar -config configfile.cfg specfile.tla

If ``-config`` isn't provided, TLC will by default look for ``specfile.cfg``. This is the file that holds all of the configuration options for the model run.

TLC has other flags, but if you can't write a config format that's all moot, so let's talk about that.

.. _cfg:

Config Format
.............

The model checkeing config language ia special DSL for using TLC from the command line. It's what the toolbox abstracts away on the backend.

All config files need a ``SPECIFICATION {spec}`` line, where ``Spec`` is whatever action encompasses your initial and next states. By convention, this should be called ``Spec``, but this isn't required— useful if you want different configs to test different variations of your system.

.. todo:: Make that a tip

Invariants you want to check must be prefixed with ``INVARIANT``, temporal properties with ``PROPERTY``. Both can have commas, eg ``INVARIANT TypeInvariant, IsSafe`` is a valid line. Unlike in the toolbox, you **cannot** make expressions invariants— they must be named operators.

.. note:: Why does that work in the toolbox? When you make an expression an invariant, the Toolbox makes a separate ``MC.tla`` file, adds that expression as an operator, and then model checks ``MC.tla`` with the new operator as an invariant. It does a similar thing to get around restrictins on constant expressions, below.

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


Config files may also have ``CONSTRAINT``, ``ACTION-CONSTRAINT``, ``VIEW``, which work equivalently to their `Toolbox options <topic_toolbox>`. 

.. todo:: Symmetry sets


TLC Options
-----------

Now that we know how to run a config file, let's get back to the TLC options. You can read all of them with ``java -jar tla2tools.jar -help`` (*not* ``-h``), or by reading them `here <tlc_page>`. Most of them are self-explanatory or equivalent to toolbox options. See the `Toolbox topic <topic_toolbox>` for more information on how to use them. The main things of note are:

- ``dump``: TODO
- ``metadir``:






.. _pcal_manual: TODO
.. _tlc_page: TODO