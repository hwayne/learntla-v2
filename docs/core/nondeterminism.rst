.. _chapter_nondeterminism:

##################
Nondeterminism
##################

Nondeterminism
=================

So far all of our specs have been **deterministic**. While there are multiple possible starting states, the behavior from each starting state is fixed. Most systems aren't deterministic. Some examples:

- Randomness creates a new possible behavior for each possible random value.
- Interactive systems aren't deterministic, since we don't know what the user is going to do and in what order they do it.
- We might know the range of readings a sensor could get, but not what specific reading it *will* get.
- If the system has many moving independent parts, we don't know in which order they'll run.

The last case, concurrency, we'll cover in the :doc:`next chapter <concurrency>`. To handle the rest, PlusCal has a couple of new constructs.

.. index:: with; nondeterministic

.. _nondet_with:

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

.. tip:: You can combine deterministic and nondeterministic assignments in a single ``with`` statement. The following is valid:

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

.. note:: If the variable set is empty, the ``with`` will block, which can lead to a `deadlock <deadlock>`. We'll talk about deadlocks more in the :doc:`next chapter <concurrency>`, when we cover concurrency.

.. index:: either
.. _either:

either-or
----------

``either`` is nondeterministic control flow. 

::

  either
    approve_pull_request();
  or
    request_changes();
  or
    reject_request();
  end either;
    
On evaluating this, TLC will create three branches:

.. digraph:: either
  :name: tmp_link
  :class: align-default
  :caption: 

  branch[label=either, shape=point];
  A -> branch[arrowhead=none, label=either];
  branch -> {approve request reject};

You *can* have labels inside an either statement. Either statements are especially useful for implementing `state machines <topic_state_machines>`. 


Using Nondeterminism
--------------------

Nondeterminism is the first major break between specifications and programming languages. It's also the first thing that significantly raises our level of abstraction. In particular, it lets us abstract over "sad paths" in our program.

Say we're specifying a large business workflow, and as one step in it, an employee requests access to a resource. In the happy path, she makes the request, it's assigned to her, and the workflow continues. There are many business reasons the assignment might be rejected:

* The employee isn't authorized to use the resource
* The resource is in use and cannot be reassigned until it's free
* The resource can only be assigned if a CI check passes, and it failed
* The request was rejected by a higher-up
* The code to reassign the resource had a bug and crashed

To fully represent all of these possible error states, we'd have to include a *lot* of information in our specification: the authorization policies, reserve policies, the CI process, checkout code, etc. Not to mention all of the other possible errors! This is a *lot* of work, and if the resource checkout is only a small part of our workflow, then it's a lot of work that *could* have been spent on studying the bigger picture.

This is where nondeterminism is really useful. We don't *need* to put in the details for all those errors. We only need to say the assignment succeeds, *or* there's an error:

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
    or
      \* some other error
      skip;
    end either;
  end macro;

``either or skip`` is a common nondeterminism pattern and it's quite useful in a lot of places.

We can also use nondeterminism to represent outside actions. If we're modeling requests that are coming into a system, we don't need to pick a specific request to spec. Instead we can define a ``RequestType`` and pull from that on every inbound request.

::

  RequestType == [from: Client, type: {"GET", "POST"}, params: ParamType]
  
  with request \in RequestType do
    if request.type = "GET" then
      \* get logic
    elsif request.type = "POST" then
      \* post logic
    else
      \* something's wrong with our spec!
      assert FALSE;
    end if;
  end with;

.. todo:: Find a good conclusion

Example: A Calculator
=======================

One way we use nondeterminism is to simulate user input. Our system has to handle all user actions properly, so we model them as nondeterministically taking actions from a valid set. As an example, let's specify an extremely simple calculator. While TLA+ can't represent decimal numbers, we can do addition, multiplication, and subtraction. First, let's allow users to add any digit to a current sum:

.. spec:: calculator/1/calculator.tla
  :name: calculator_1

.. todo:: This example might work better if I break the ``while`` into a separate step. But that's for after v2 is up and I'm polishing— might be totally unnecessary.

Two things to notice:

1. The user can input any single digit, which is represented with a ``with``. We restrict their options to ``0..9`` to keep the state space smaller.
2. We restrict the spec to only ``NumInputs`` operations per behavior. If we instead did ``while TRUE``, ``sum`` would be unbounded, the state space would be infinitely large, and the model checker would run forever. I do make ``NumInputs`` a `constant` for easy modification.

For all this spec, I'm using ``NumInputs <- 5``, for :ss:`calculator_five_inputs_no_either`. This is a much higher ratio of (seen states / distinct states) than we've seen before: adding 5 and then 3 gives the same state as adding 3 and then 5. There's also a much higher ratio of (seen states / initial states). Before, we only had one behavior from each starting state, but now we have many.

To allow users to also subtract and multiply, we can place the addition logic in an ``either`` branch, and then create two more branches.


.. spec:: calculator/2/calculator.tla
  :diff: calculator/1/calculator.tla
  :name: calculator_2

Allowing a nondeterministic choice of operator bloats the state space further :ss:`calculator_five_inputs_with_either`. When dealing with nondeterminism, there are lots of possible states, which is one reason it's harder to reason about.

Normally we'd write an invariant to test that this spec is working correctly, but aside from a type invariant or two there's not much to check here. So let's instead turn things around and see if we can use TLA+ to *find* a solution to something. Can we reach some number, say ``417``, in five inputs?

To find this, let's add an invariant saying ``sum`` is *not* 417. Then, if ``sum`` is reachable, the model checker will *fail*, and give us an error trace representing a path to 417.

.. spec:: calculator/3/calculator.tla
  :diff: calculator/2/calculator.tla

Now running the checker with ``INVARIANT Invariant`` and ``NumInputs <- 5, Target <- 417``, we get this error trace:


.. code-block::

  State 1: 
  /\ sum = 0
  /\ i = 0

  State 2:
  /\ sum = 1
  /\ i = 1

  State 3:
  /\ sum = 10
  /\ i = 2

  State 4:
  /\ sum = 60
  /\ i = 3

  State 5:
  /\ sum = 420
  /\ i = 4

  State 6:
  /\ sum = 417
  /\ i = 5

.. todo:: Here would be a good place to talk about auxiliary variables, so that we can see what operation actually happened

So 417 is ((((0+1)+9)*6)*7)-3.

(This spec got me curious: what's the *smallest* number we can't reach in 5 inputs? There's no *easy* way to do this as a single model-check. Instead I wrote a script to run the model checker `from the command line <topic_cli>` with every value of ``Target`` from 0 to 1000. The first number that doesn't produce an error trace is 851.)

Summary
==========

* Nondeterminism is when the spec can do one of several different things in one step.
* ``with x \in set`` nondeterministically chooses a value from ``set`` for ``x``.
* ``either branch1 or branch2`` nondeterministically chooses a branch to execute.
* Nondeterminism can be used to abstract implementation details into a high-level step.
