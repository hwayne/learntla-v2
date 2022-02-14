.. _overview:

+++++++++++++++++++
Conceptual Overview
+++++++++++++++++++

Intro
Bank account

There is some :dfn:`state`, the accounts and outstanding wires, and many ways the system can evolve from there. We call each possible timeline a :dfn:`behavior`. One behavior of the system is

#. Bob and Alice both have 6 dollars.
#. Alice wires Bob 2 dollars.
#. Alice now has 2 dollars, Bob has 9 dollars.

Another behavior is

#. Bob and Alice both have 5 dollars.
#. Alice wires Bob 10 dollars.
#. We check and learn that Alice doesn't have enough money, and the transaction fails.
#. Alice and Bob bot have 5 dollars.

(Notice that they start with a different amount: we can have multiple possible starting states with different behaviors.)

Or even

#. Bob and Alice both have 5 dollars.
#. Alice wires Bob 5 dollar in two separate transactions.
#. Both account checks happen before either withdrawal is processed, so both wires succeed.
#. Alice now has -5 dollars, Bob has 15 dollars.

That's a behavior you don't want! If it's possible for the system to do that, then there's something wrong with the design of your system. We say the system violated a :dfn:`property`. In this case, the property might be:

**NoOverdrafts Property**: Nobody's bank account can ever be negative.

Note we didn't specify *who's* bank account can't be negative, it's everyones. This particular property is also an :dfn:`invariant`: a property that must hold *for every single state in the behavior*. Many properties we care about are invariants. But not all. Consider the following behavior:

#. Bob and Alice both have 6 dollars.
#. Alice wires Bob 2 dollars.
#. We pull two dollars out of Alice's account and get ready to put 2 in Bob's account.
#. The server explodes. / The code hits an infinite loop and spins endlessly
#. Alice now has 4 dollars, Bob has 6 dollars.

There's no *individual* state that causes a problem, but something went wrong overall. A property like "All wires either eventually fully complete or fully rollback" isn't an invariant, but a more general "temporal property".

.. note:: we call properties like this "liveness properties", because that's the term the original proposers of this idea used. There are other kinds of properties besides invariants and liveness, and we cover a few of those in an `advanced section <action-properties>`.

.. exercise:: think of some invariants of a system you run.


Specifications
---------------

Let's stick to states, behaviors, and invariants right now. We have a system and want to know if it's designed in a correct way: it doesn't break any of our invariants. So we need to specify the possible starting states, the things the system can do ("actions"), and the things it needs to guarantee. This description is called a :dfn:`specification`. Once we have a specification, we can use a "model checker" to see if any of the possible behaviors break the invariant.


Here's what a specification looks like in TLA+. Don't worry too hard about understanding the syntax: this is, after all, a conceptual overview. Instead, see if you can pick out what the things correspond to.

.. todo:: spec

Toodles :ss:`wire_overview` moodles
