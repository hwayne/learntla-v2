.. _chapter_overview:

+++++++++++++++++++
Conceptual Overview
+++++++++++++++++++

{{ ALL THIS IS DRAFT }}
.. todo:: THIS

To justify the value of TLA+, let's talk about how it's useful, and how it's different from programming languages.

Imagine we're building a wire transfer service for a bank. Users can make transfers to other users. As a requirement, we don't allow any wires that would overdraft the user's account, or make it go below zero dollars. At a high level, the could would look like this:

.. code-block::

  def transfer(from, to, amount)
    if (from.balance <= amount) # guard
      from.balance -= amount;   # withdraw
      to.balance += amount;     # deposit


This would satisfy the requirement: if you try to transfer more than you have, the guard prevent you.

Now consider two changes:

1. Users can start more than one transfer at a time.
2. Transfer steps are nonatomic. TK

Neither change, by itself, causes a problem. But both of them *together* leads to a possible race condition:

#. Alice has 6 dollars in her account, and makes two transfers to Bob. Transfer X is for 3 dollars, and transfer Y is for 4 dollars.
#. Guard(X) runs. Because 3 < 6, we go on to Withdraw(X).
#. *Before Withdraw(X) happens*, Guard(Y) runs. Because 4 < 6, we go on to Withdraw(Y).
#. Both withdrawals run, taking 7 dollars out of Alice's account and leaving her with -1.

If Withdraw(X) happens before Guard(Y), then there's no problem; transfer Y will simply fail. Race conditions like this are fundamentally rare: *most* of the time, the program will behave as expected and maintain our properties. It's only in very particular orderings of events that we have a bug. That's why concurrency errors are so far hard to find.

.. todo:: Exploring situations in the design space. If we have only one, then the issue goes away. Because they're so rare, though, you don't know that you've solved it for certain, only that you don't see it anymore.

The purpose of TLA+, then, is to automate finding these design issues. We want to give the tooling a system and a requirements and it can tell us whether or not we can break the requirement. If it can, then we know to change our design. If it can't, we can be more confident that we're correct.

Structure
---------

So there's three parts to our conceptual framework <<.

First, we need to describe the system and what it can do. This is called the **specification**, or spec. Our design might look like this:

* We have a set of accounts. Each account has a number, representing the balance.
* Any account can attempt to transfer any amount of money to any other account. 
* A transfer first checks if there are sufficient funds. If there are, the amount is subtracted from the first account and added to the second.
* Transfers are nonatomic. Multiple transfers can happen concurrently.

The specification has a set of "behaviors", or possible distinct executions. For the spec to be correct, every behavior must satisfy all of our system requirements, or **properties**. "No account can overdraft" is an example property, and is violated if there's a behavior of the spec has a state where an account has a negative balance. It doesn't matter if all of the other possible behaviors *don't* have overdrafts. we're looking for rare design error, so just one violation is enough.

.. note:: "No account can overdraft" is an **invariant** property, which is one that must be true of every single state of every single behavior. There are other, more advanced properties, like `liveness <chapter_temporal_logic>` and `action <chapter_action_properties>` properties, which we'll cover in time.

Once we've written a spec and properties, we feed them into a "model checker". The model checker takes the spec, generates *every possible* behavior, and sees if they all satisfy all of our properties. If one doesn't, it will return an "error trace" showing how to reproduce the violation. There are a couple different model checkers for TLA+, but the most popular one is TLC, which is bundled with the toolbox. Unless I say otherwise, when I talk about model checkers I'm referring to TLC.

Now we can't check *every* possible behavior. In fact there's an infinite number of them, since we can also add more accounts and transfers to the system. So we instead check all the behaviors under certain constraints, such as "all behaviors for three accounts, of up to 10 dollars in each account, and two transfers, of up to 10 dollars in each transfer." We call this set of runtime parameters, along with all the other model checker configuration we do, the **model**.

.. todo:: This means that a passing model doesn't guarantee the spec is correct. Maybe there's an error that only appears with larger parameters. But empirically, in specification we've found that most errors appear with very small scopes: if a system works with 3 workers, it'll probably also work with 25 workers.



Specifications
---------------

So what does this all look like in practice? Let's present a spec for wire transfers, first with hardcoded parameters and then with model-parameterizable ones.

.. spec:: wire.tla

Over the rest of the book I'll be covering how all of this works syntactically. For now I just want to call attention to various parts that TLA+ does different from code:

* Definitions use ``==``. Sorry I don't make the rules
* ``People`` and ``Money`` are `sets <set>`, collections of unique and unordered values. While programming languages mostly use arrays and key-value maps (`sequence` and `struct` respectively), sets are a lot more foundantional in specification.
* ``[People -> Money]`` is also a set (in this case, a `function_set`). It represents *all possible assignments* of people to money amounts: alice has 5 dollars and bob 1, alice 10 dollars and bob 6, etc. 
* The variable ``acct`` isn't a fixed value, it is one of 100 different values, one for each element of ``[People -> Money]``. When we model check this, TLC will explore every possible behavior starting from every one of these 100 possible initial values.
* ``NoOverdrafts`` is a `quantifier <\A>`. It's true if *every* account is >= 0 and false otherwise. In python, this might be equivalent to ``all([acct[p] >= 0 for p in People])``. Quantifiers are an extremely powerful feature of TLA+, making it easy to write very complex properties.
* We have more than one ``wire`` `process` running simultaneously. With ``NumTransfers == 2``, there are two processes in the spec. But we can choose to have ten, a hundred, or a thousand processes if we really want, our only limit is our CPU time.
* Each step of the algorithm belongs to a separate `label`. In TLA+ we are very explicit about concurrency and atomicity. That lets us 


Models
......



TLA+ makes it very easy to change our designs.

Test with the fixed 

Toodles :ss:`wire_overview` moodles


.. note:: If you want to run this yourself, see `setup`. You're not expected to learn

Components
-----------

Let's now break down the specifics of the specification. We'll be going into details about all of these in the next few sections.

* ``---- MODULE and end module ----``

.. spec:: wire.tla

In that, we just noted how various parts of the spec corresponded to the concepts we are dealing with. Now it's time to discuss how it works syntactically. 

Models
---------
