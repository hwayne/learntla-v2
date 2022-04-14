.. _chapter_nondeterminism:

##################
Nondeterminism
##################

In this chapter we will cover

- nondeterminism
- either
- with (again)


Nondeterminism
=================

So far all of our specs have been **deterministic**. While there are multiple possible starting states, the behavior from each starting state is fixed. Most systems aren't deterministic. Some examples:

- Randomness creates a new possible behavior for each possible random value.
- Interactive systems aren't deterministic, since we don't know what the user is going to do, and in what order they do it.
- We might know the range of readings a sensor could get, but not what specific reading it *will* get.
- If the system has many moving independent parts, we don't know in which order they'll run.

The last case, `concurrency`, we'll cover in the next chapter. To handle the first two cases, PlusCal has a couple of new constructs:

.. constructs

.. index:: with; nondeterministic

with
-----------

We've already seen `with` used to create local variables:

::

  with tmpx = x, tmpy = y do
    y := tmpx;
    x := tmpy;
  end with;

Remember how, when defining the spec variables, we can write ``x \in set`` instead of ``x = val``? We can do the same here, too.

::

  with roll \in 1..6 do
    sum := sum + roll;
  end with;

Inside this block, ``roll`` can be any one of those six values. The model checker will try *all six*, effectively creating six new behaviors from that single statement. 
The ``with`` set can also be a variable. If the set is empty, then the ``with`` blocks. This can lead to deadlocks, too.

.. tip:: You can combine deterministic and nondeterminsitic assignments in a single ``with`` statement. The following is valid:

  ::

    with
      x \in BOOLEAN,
      y \in 1..10,
      z = TRUE
    do
      \* ...
    end with;



You can also nondeterministically pull from a variable set:

::

  with thread \in sleeping do
    sleeping := sleeping \ {thread};
  end with;

.. note:: If the variable set is empty, the ``with`` will block, which can lead to a `deadlock <deadlock>`. We'll talk about deadlocks more in the `next chapter <chapter_concurrency>`, when we cover concurrency.

.. index:: either
.. _either:

either-or
----------

``either`` is nondeterminsitic control flow. It lets us write one of severla things happens: 

.. todo:: example


You *can* have labels inside an either statement.
write or skip


Using Nondeterminism
--------------------

Nondeterminism is the first major break between specifications and programming languages. It's also the first thing that significnatly raises our level of abstraction. In particular, it lets us abstract over "sad paths" in our program.

Say we're specifying a large business workflow, and as one step in it, an employee requests access to a resource. In the happy path, she makes the request, it's assigned to her, and the workflow continues. There are many business reasons the assignment might be rejected:

* The employee isn't authorized to use tha resource
* The resource is in use and cannot be reassigned until it's free
* The resource can only be assigned if a CI check passes, and it failed
* The request was rejected by a higher-up
* The code to reassign the resource had a bug and crashed

To fully represent all of these possible error states, we'd have to include a *lot* of information in our specification: the authorization policies, reserve policies, the CI process, checkout code, etc. Not to mention all of the other possible errors! This is a *lot* of work, and if the resource checkout is only a small part of our workflow, then it's a lot of work that *could* have been spent on studying the bigger picture.

This is where nondeterminisim is really useful. We don't *need* to put in the details for all those errors. We only need to say the assignment succeeds, *or* there's an error:

::

  macro request_resource(r) begin
    either
      reserved := reserved \union {r};
    or
      \* Request failed
      skip;
    end either;
  end macro;

If we need to also model the type of error (if that affects our recovery logic), we can represent exactly as many as we care about:

::

  macro request_resource(r) begin
    either
      reserved := reserved \union {r};
      failure_reason := "";
    or
      with reason \in {"unauthorized", "in_use", "other"} do
        failure_reason := reason;
      end with;
    end either;
  end macro;

.. todo:: More


Example
===========
.. using nondeterminism

.. example


.. fifteen algorithm?
.. todo:: IsUnique(<<x, y, z>>)

TK
Lets us 

