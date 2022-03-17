.. _chapter_concurrency:

################
Concurrency
################

In this chapter we will cover

- concurrency
- processes
- await
- deadlocks
- either
- with
- procedures

So far we've only worked with single-process algorithms.


.. Needs LOTS of exercises

.. index:: process
  :name: process

.. _processes:

Processes
=============

Processes are the main agents of concurrency. They usually represent independent programs, but can be used more broadly, too. Let's start with one process.

.. spec:: reader_writer/1/reader_writer.tla

:ss:`rw_1` Identical to no processes, except the ``end process``. Note it's assigned to a value, ``1``. This will be important later. Now let's add another process, one to read from the queue and finish.

.. spec:: reader_writer/2/reader_writer.tla
  :diff: reader_writer/1/reader_writer.tla


.. note:: All processes must have comparable types: all integers, all strings, all sequences, etc. The one exception is that processes can also be `model_values`, which will be covered in the `next chapter <chapter_constants>`.

The writer has a single action, ``Write``, and the reader has a single action, ``Read``. We haven't specified which should happen first, so the two can happen in any order. Either we (1) write to the queue and then read from it, or (2) read from the queue and then write to it.

.. warning:: Different processes cannot share label names.

Behavior (2) doesn't make any sense: how can we read from the queue if there's nothing already in it? And if you try to run the spec, TLC will raise this as an error.

| Error: TLC threw an unexpected exception.
| This was probably caused by an error in the spec or model.
| See the User Output or TLC Console for clues to what happened.
| The exception was a tlc2.tool.EvalException
| : Attempted to apply Head to the empty sequence.

It's an "unexpected exception", but it points to a real flaw in our system: we don't specify what should be possible in the case of attempting to read from an empty queue. There's a lot of different things we could *choose* to do:

* We could simply skip the dequeueing logic and continue the process.
* We could block the reader until the queue is nonempty.
* We could substitute in a default value.
* We could raise an error *as part of the system*, as opposed to having TLC treat it as a flaw in the system.

.. tip:: Regularly model check your specs, even if you haven't figured out your invariants yet. It's good to catch these kinds of ambiguous cases early.

The point is that we decide what's the right choice based on what we need from the system. For now, let's have the reader ignore empty queues, by wrapping the logic in an ``if`` block.

.. spec:: reader_writer/3/reader_writer.tla
  :diff: reader_writer/2/reader_writer.tla

This passes :ss:`rw_2`.

local variables
-----------------

Let's modify the writer so it can write twice, instead of once.

TK while loop

Notice how many more states we have :ss:`rw_local_1`. The ``while`` loop is nonatomic, and every iteration counts as a separate ``Write`` action. So there are now three possible orderings: Read-Write-Write, Write-Read-Write, and Write-Write-Read.

``i`` is only used in the writer, so we don't necessarily need to expose it to the reader. We can make a variable local to the process, like this:

TK local_2
ss rw_local_2

As with global variables, we can have multiple starting local variables— ``i \in 1..3`` is valid.

In practice, local variables aren't often used, as they can't be placed in `define` blocks. This means you can't easily typecheck them, write helper operators, etc. Generally we use local variables for "bookkeeping" variables, like loop iterations and TK.

.. todo:: better example of bookkeeping variable

For now let's pull out the ``while`` loop and go back to version TK.

Process Sets
---------------------

Once we have a single process, we can extend it into a process set. Instead of saying ``process name = val``, we write ``process name \in val``. Then PlusCal will create one distinct process for *each* value in the set.

TK three_writers

W1-W2-W3-R, W2-W1-W3-R, W1-W3-W2-R...

.. tip:: ``pc`` *can* be used in `define` blocks.

.. todo:: ``pc``, functions

.. index:: self
  :name: self

We're now adding up to three values to the queue, but we're only reading one value. 
In process sets have a special keyword ``self``, which retrieves the value of the 

.. TK online [w \in Writers > TRUE] online[self] := FALSE

.. tip:: 

  Macros *can* use the value of self inside of them. In the above spec, the following would be valid::

    macro turn_off() begin
      online[self] := FALSE;
    end macro;

  Then we can call ``turn_off()`` inside a writer process.

.. todo:: Come up with some exercises


.. -----------------------

.. index:: await
  :name: await

await
---------

The current spec ignores logic when the queue is empty. Earlier I proposed some other options. Of them, it's "straightforward" to TK. What about having the reader *wait* for something to enter the queue?

await version

``await`` is a *restriction* on when the label can run. The label can only run— the state "committed", if you will— if *every* ``await`` statement in the label evaluates to true.

.. warning:: ``await`` interacts a little oddly with variable updates— it will be based on the updated value if directly embedded but not if the variable is used via a ``defined`` operator. This is due to the PlusCal->TLA+ translation grammar. As a general precaution, don't use updated variables in ``await`` statements.

.. todo:: writer also blocks

.. index:: deadlock
  :name: deadlock

What if it's impossible for a label to *ever* be evaluated? For example, in this spec::

  process x = "x"
  begin
    X:
      await FALSE;
  end process;

Procedures
-----------

*Note: this is both fairly complicated and fairly niche, so feel free to skip this and come back to it later.*

todo explain
``EXTENDS sequences``


Nondeterminism
=================


either-or
----------

with
-----------

.. index:: threads
  :name: threads

Example
============



Summary
============
