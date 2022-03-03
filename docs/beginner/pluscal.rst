
.. _foo:

++++++++++++++++++++++++
Writing Specifications
++++++++++++++++++++++++

Overview
===========
In the last section, we introduced operators, sets, and values, and did some simple computation with them. Now that we have that groundwork done, it's time to actually talk about specifications.

For a specification

.. _pluscal:

PlusCal
-----------

TLA+ is the *Temporal Logic of Actions*, where the "actions" are descriptions of state changes in the system. It's a powerful way of expressing mutation, but it is also very general, accepting a large degree of complexity to be able to express more powerful systems. Many engineers struggle to start learning it. So in 2009, Leslie Lamport created a DSL called :dfn:`PlusCal`: a more programming-like syntax that compiles to TLA+ actions.

PlusCal isn't as powerful as "raw" TLA+, and there are some types specifications you cannot write in it. But for many other kinds of specifications, it is *simpler* than doing everything in TLA+, and it is easier to learn. In my experience as an educator, I've found that most programmers have an easier time learning PlusCal and then raw TLA+ than they do if they start with raw TLA+. So the rest of the beginner part of this text will use PlusCal.

.. note:: If you're more mathematically inclined, or already know PlusCal and want to jump further, you can check out `pluscal-to-tla`.

PlusCal
============

Let's start with a very simple spec:

.. spec:: pluscal.tla

Inside the comment block (``(* *)``) is our PlusCal algorithm. We need to do this because this is a valid TLA+ file; the pluscal algorithm will be compiled to TLA+ below. The algorithm must start with ``--algorithm $name``, otherwise it will be treated like a regular comment. Unlike the module name, the algorithm ``$name`` doesn't need to correspond to anything, and can be ``foo`` for all anyone cares.

Next, we have a variables block. Any TLA+ value can be a variable. We open the body of the algorithm with ``begin`` and close it with ``end algorithm``. Inside that we have two :dfn:`labels`, ``A`` and ``B``, which we will discuss more in the next section. Inside the labels we have update statements, which use ``:=``. ``:=`` is **only** used when we have an existing variable and want to update its value. Otherwise, we use ``=``.

Once we have the algorithm, we need to translate it to TLA+. We can do this in the menu bar:

.. todo:: IMG


Alternatively, we can use :kbd:`cmd-T` on Mac or :kbd:`ctrl-T` on Windows and Linux. This puts a translation below the comment block:

::

  \* BEGIN TRANSLATION
  \* \* A bunch of TLA+ code
  \* END TRANSLATION


That's what's actually run when we model check this spec.

.. troubleshooting:: No translation

  Put the translation below the ``====``

.. troubleshooting:: Model Checking

  If the blah blah blah

.. _labels:
.. _label:

Labels
------------

We're learning TLA+ to work on complex systems, so let's frame the motivation and existence of labels in that context. What are we building up to?

Complex systems have lots of *concurrency*, and many things are going on at once. Events aren't instantaneous, and may take some time to complete. But they will take different lengths of time. 

1. Summing a list of 100 numbers
2. In something like ``http.get(website, auth)``, some time will pass between making the HTTP request and receiving a response. 

The first line of code takes tens of nanoseconds to run, and the second tens of milliseconds. That's a time difference of six orders of magnitude. It might be possible for the summation to happen in between the request and response, but it's virtually impossible for the HTTP request to happen in between starting and finishing the summation. In our system, the first event would be "instantaneous", while the second would not.

Which brings us to labels. Labels represent everything that can happen in a single step of the system. If I write

::

  Label1:
    x := Sum(seq);

I am saying that the summation happens in a single step, and no time passes between the start and end of the summation. By contrast, if I write

::
  
  SendRequest:
    \* blah blah blah
  GetResponse:
    \* blah blah blah

Then *time passes* between ``SendRequest`` and ``GetResponse``.

.. note:: actions

If I wanted to, I could *choose* to make the summation nonatomic. Here's how I'd do it in PlusCal:

::

  Sum:
    while i <= Len(seq) do
      x := x + seq[i];
      i := i + 1;
    end while;
    
We'll talk about the nuances of `while` later, but the basic idea is that now *each iteration* of the summation is nonatomic. We could add two numbers, start an http request, add two more, receive the response, and add the rest. Or we could add them all before both steps of the http, or all after. Concurrency is weird.

The point is this: the labels let us specify just how concurrent our system is. If we want to express that something is atomic, we can do that. If we want it to be interruptable, we can do that too.

.. todo:: conclusion

Label Rules
--------------

We're modeling time here, so there are restrictions on what we can o

#. All statements must belong to a label. This means, among other things, that you miust always start the algorithm with a label.
#. All statements must *unambiguously* belong to a label. If any part of an ``if`` block contains a label, then you *must* have a label after the end of the whole ``if`` block.

  Not all blocks have to have the *same* number of labels! Conditionals trigger different behavior, which can take different amounts of time.

#. Any variable can only be updated once per label. Otherwise,
#. You must always precede a ``while`` statement with a label.
#. Macros and ``with`` statements cannot have labels.


..
  * If
  * While
  * define
  * with
  * macro
  * skip
  * assert
  * label rules

A Duplication Checker
======================

Multiple Starting States
-------------------------

:dfn:`behavior`

.. todo:: Bubblesort eff yeah
