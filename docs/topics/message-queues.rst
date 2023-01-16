.. _topic_message_queues:


########################
Modelling Message Queues
########################

This is the most common "pattern" for distributed systems.

We'll assume there's a set of ``Reader`` processes and ``Writer`` processes sharing a single queue. Later we'll discuss how to extend this to multiple queues.

The Queue
=========

For now let's consider a perfect FIFO queue, with the operations to push new messages and pop old ones.

The ``queue`` variable is generally a `sequence <sequence>` of message `structs <struct>`. To write a new message, we just do ``queue := Append(queue, msg)`` (or ``queue' = ...``). There's an easy way and a hard way to read from a queue.

The *easy* way is to destructively update the queue, so that the newest message is always ``Head(queue)``. This is conceptually simple, and it's easy to do things like check if the queue is empty and write a type invariant (see below). The one downside is that you can't write properties that rely on the queue's history, like "the same message is never enqueued twice". You'd be able to see if duplicates are on the queue at the same time, but not that a duplicae was pushed after the original was popped. At least, not without a `history queue <topic_aux_vars>`. 

The *hard* way is to make the queue immutable. You append to the queue like normal, but have an additional ``i`` variable representing the next message to read. To "pop" a message, increment ``i``. This is harder to work with, adds variable bloat, and makes a lot of simple queue checks (like getting the length) more awkward. The one upside is that you preserve the whole queue history, making generalized properties easier.

.. warning:: Be careful of unbound models with immutable queues! Even if you bound the maximum number of unread messages, the queue can still grow without, as long as you keep reading old messages.

As a rule of thumb, I like using immutable queues for ones that I don't plan to append to, such as ones initialized by multiple starting states.

Here's a quick table of basic operations for both styles:

.. list-table:: 
  :header-rows: 1

  * - Operation
    - Mutable Queue
    - Immutable Queue
  * - Get Current Message
    - ``Head(queue)``
    - ``queue[i]``
  * - Delete current message
    - ``queue' = Tail(queue)``
    - ``i' = i + 1``
  * - Size of queue
    - ``Len(queue)``
    - ``Len(queue) - i + 1``
  *
    - Is queue empty?
    - ``queue = <<>>``
    - ``Len(queue) = i + 1``


The Messages
============

Use a set of structs.

::

  \* Seq comes from EXTENDS Sequences
  QueueType == Seq(MessageType)
  MessageType == [id: Nat, from: Writer, data: DataType]

Having an ``id`` field is good practice because it lets you distinguish difference messages with the same content (make sure to have a ``MaxId`` constant!). ``DataType`` can also be a struct. If you want to have multiple distinct kinds of messages, add an additional ``msg`` field and push the details of the data to the ``data`` struct. Then make the ``MessageType`` a union of the possible subtypes:

::

  AlphaMsg == [id: Nat, from: Writer, msg: {"alpha"}, data: AlphaData]
  BravoMsg == [id: Nat, from: Writer, msg: {"bravo"}, data: BravoData]
  Messagetype == AlphaMsg \union BravoMsg
  

Additional Complexities
=======================

Multiple Reader Queues
----------------------

As `discussed in tips <decompose_structs>`, the best way to represent complex data per process is to decompose the variables into separate functions. In other words, if each reader has a queue, the appropriate representation is:

::

  queues \in [Reader -> QueueType]

Each reader then reads from ``queues[self]``. To write the same message to every queue, we redefine the ``queues`` variable:

::

  \* PlusCal
    queues := [r \in Reader |-> Append(queues[r], msg)]
  \* TLA+
    queues' = [r \in Reader |-> Append(queues[r], msg)]

If you want to push to only a *subset* of readers, we can do this with function merge:

::

  \E readers \in SUBSET Reader:
    queues' = [r \in readers |-> Append(queues[r], msg)] @@ queues

.. tip:: At-most-once delivery can be modeled as delivering to a subset of a valid recipients. Everything outside the subset doesn't receive the intended message.

Multiple Writer Queues
-----------------------

This is the same as multiple reader queues, except the question is how do we *read* nondeterministically from a queue.

::

  \* PlusCal
    with w \in Writer:
      msg := Head(queue[w]);
      queue[w] := Tail(queue[w]);

  \* TLA+
    \E w \in Writer:
    /\ msg' = Head(queue[w])
    /\ queue' = [queue EXCEPT ![w] = Tail(@)]
