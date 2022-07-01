.. _chapter_overview:

+++++++++++++++++++
Conceptual Overview
+++++++++++++++++++


.. todo:: Mention the name TLC

To justify the value of TLA+, let's talk about how it's useful, and how it's different from programming languages.

Imagine we're building a wire transfer service for a bank. Users can make transfers to other users. As a requirement, we don't allow any wires that would overdraft the user's account, or make it go below zero dollars. At a high level, the could would look like this:

.. code-block::

  def transfer(from, to, amount)
    if (from.balance >= amount) # guard
      from.balance -= amount;   # withdraw
      to.balance += amount;     # deposit


This would satisfy the requirement: if you try to transfer more than you have, the guard prevents you.

.. todo:: {Inkscape} Diagram of system

Now consider two changes:

1. Users can start more than one transfer at a time.
2. Transfer steps are nonatomic. One transfer can start and (potentially) finish while another transfer is ongoing.

Neither change by itself causes a problem. But both of them *together* leads to a possible race condition:

#. Alice has 6 dollars in her account, and makes two transfers to Bob. Transfer X is for 3 dollars, and transfer Y is for 4 dollars.
#. Guard(X) runs. Because 3 < 6, we go on to Withdraw(X).
#. *Before Withdraw(X) happens*, Guard(Y) runs. Because 4 < 6, we go on to Withdraw(Y).
#. Both withdrawals run, taking 7 dollars out of Alice's account and leaving her with -1.

.. todo:: {GRAPH} error

If Withdraw(X) happens before Guard(Y), then there's no problem; transfer Y will simply fail. Race conditions like this are fundamentally rare: *most* of the time, the program will behave as expected and maintain our properties. It's only in very particular orderings of events that we have a bug. That's why concurrency errors are so far hard to find.

That's also why they're hard to fix. Imagine if we added a third feature, say a lock in the right place, to fix the bug. Does the issue go away because we've solved it, or because we've made it rarer? Without being able to explore the actual consequences of the designs, we can't guarantee we've solved anything.

The purpose of TLA+, then, is to programmatically explore these design issues. We want to give the tooling a system and a requirements and it can tell us whether or not we can break the requirement. If it can, then we know to change our design. If it can't, we can be more confident that we're correct.

Structure
---------

So there's three parts to the conceptual framework of TLA+.

First, we need to describe the system and what it can do. This is called the **specification**, or spec. Our design might look like this:

* We have a set of accounts. Each account has a number, representing the balance.
* Any account can attempt to transfer any amount of money to any other account. 
* A transfer first checks if there are sufficient funds. If there are, the amount is subtracted from the first account and added to the second.
* Transfers are nonatomic. Multiple transfers can happen concurrently.

The specification has a set of "behaviors", or possible distinct executions. For the spec to be correct, every behavior must satisfy all of our system requirements, or **properties**. "No account can overdraft" is an example property, and is violated if there's a behavior of the spec has a state where an account has a negative balance. It doesn't matter if all of the other possible behaviors *don't* have overdrafts. we're looking for rare design error, so just one violation is enough.

.. todo:: {GRAPH}

  .. digraph:: G

    node[label=""]

    A -> B -> C;

  Each box is a state. Any sequence of boxes and arrows is a behavior. The set of all behaviors forms the specification.

.. note:: "No account can overdraft" is an **invariant** property, which is one that must be true of every single state of every single behavior. There are other, more advanced properties, like `liveness <chapter_temporal_logic>` and `action <chapter_action_properties>` properties, which we'll cover in time.

Once we've written a spec and properties, we feed them into a "model checker". The model checker takes the spec, generates *every possible* behavior, and sees if they all satisfy all of our properties. If one doesn't, it will return an "error trace" showing how to reproduce the violation. There are a couple different model checkers for TLA+, but the most popular one is TLC, which is bundled with the toolbox. Unless I say otherwise, when I talk about model checkers I'm referring to TLC.

Now we can't check *every* possible behavior. In fact there's an infinite number of them, since we can also add more accounts and transfers to the system. So we instead check all the behaviors under certain constraints, such as "all behaviors for three accounts, of up to 10 dollars in each account, and two transfers, of up to 10 dollars in each transfer." We call this set of runtime parameters, along with all the other model checker configuration we do, the **model**.

.. note:: This means that a passing model doesn't guarantee the spec is correct. Maybe there's an error that only appears with larger parameters. But empirically, in specification we've found that most errors appear with very small scopes: if a system works with 3 workers, it'll probably also work with 25 workers.



Specifications
---------------


So what does this all look like in practice? Let's present a spec for wire transfers, first with hardcoded parameters and then with model-parameterizable ones.

.. spec:: wire/1/wire.tla
  :name: wire
  :fails:

Over the rest of the book I'll be covering how all of this works syntactically. For now I just want to call attention to various parts that TLA+ does different from code:

* Definitions use ``==``. Sorry I don't make the rules
* ``People`` and ``Money`` are `sets <set>`, collections of unique and unordered values. While programming languages mostly use arrays and key-value maps (`sequence` and `struct` respectively), sets are a lot more foundantional in specification.
* ``[People -> Money]`` is also a set (in this case, a `function set <function_set>`). It represents *all possible assignments* of people to money amounts: alice has 5 dollars and bob 1, alice 10 dollars and bob 6, etc. 
* The variable ``acct`` isn't a fixed value, it is one of 100 different values, one for each element of ``[People -> Money]``. When we model check this, TLC will explore every possible behavior starting from every one of these 100 possible initial values.
* ``NoOverdrafts`` is a `quantifier <\A>`. It's true if *every* account is >= 0 and false otherwise. In python, this might be equivalent to ``all([acct[p] >= 0 for p in People])``. Quantifiers are an extremely powerful feature of TLA+, making it easy to write very complex properties.
* We have more than one ``wire`` :doc:`process </core/concurrency>` running simultaneously. With ``NumTransfers == 2``, there are two processes in the spec. But we can choose to have ten, a hundred, or a thousand processes if we really wanted, with only our patience and our RAM as limiting factors. 
* Each step of the algorithm belongs to a separate `label <label>`. The labels determine what happens atomically and what can be interrupted by another process. That way we can represent race conditions.


Models
......

Once we have our design, we can model check it against some requirements. We can make a model and say that ``NoOverdrafts`` is an invariant. Then running the model will check *every possible* way the system can evolve. If any of those ways leads to a state where ``NoOverdrafts`` is false, then the model checker will raise an error.

.. note:: If you want to run this yourself, see `setup`.

We checked it with two transfers. But what if we wanted to check it with four transfers? TLA+ makes it very easy to change our designs. We can parameterize any value, and then have different models check with different values.

.. spec:: wire/2/wire.tla
  :diff: wire/1/wire.tla
  :fails:

Now I can make separate models, with the same invariant, but different numbers of simultaneous transfers. So I can see that it works correctly with one transfer but not two. 

.. todo:: {CONTENT} Let's make a fix

Discussion
==========

There's a few concepts I haven't introduced here: temporal properties, fairness, stutter-invariance, etc. All of these will be covered later. Hopefully, though, this is enough to give you a sense of what, if you decide to learn TLA+, you'll actually be able to *do* with it. If you're interested in continuing, check out the :doc:`Core </core/index>` and `setup`.
