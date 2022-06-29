##############
FAQ
##############

These are some of the questions I get regularly asked about TLA+. If you have one you'd like to see me answer, feel free to `ask me! <https://github.com/hwayne/learntla-v2/issues>`__

Who is TLA+ For?
=================

This book will not teach you programming. It will not teach you how to test code nor how
to write mathematical proofs that your code is correct. Formally proving code correct is
much more difficult and high effort than proving designs are correct. This book will not
teach you how to directly convert TLA+ into production code. Much of TLA+’s flexibility
and power comes from it not having to match a programming language. A few dozen
lines of TLA+ can match hundreds or thousands of lines of code. No tool can replace
your insight as an engineer.
Finally, this book is not a comprehensive resource on how to use TLA+. In particular,
we focus on using PlusCal, the main algorithm language that compiles to TLA+. PlusCal
adds additional constructs that make TLA+ easier to learn and use. While powerful and
widely used in the TLA+ community, PlusCal nonetheless has a few limitations that raw
TLA+ does not.
Prerequisites
You should already be an experienced programmer. While TLA+ can be used with any
programming language, it is not a programming language. Without having something to
program with, there’s really no reason to use TLA+. With this assumption, we can also
move faster: we don’t need to learn what a conditional is, just what it looks like in TLA+.
Knowing some logic and math is going to help. You don’t have to be particularly
experienced with it, but TLA+ borrows its syntax heavily from mathematics. If you know
what (P => Q) \/ R means, you’re fine. If you don’t know, this should still be accessible,
It's awesome!

What's TLA+ good for?
=====================

What's TLA+ bad for?
====================

Test code directly
numbers
String manipulation
Probabilistic properties
Good layouts


What's TLA+ Landscape?

I've heard that TLA+ is a "formal method". What's that?
==================================================================

"Formal methods" is, very roughly, the field of computer scientist dedicated to writing correct programs. This is usually done by first writing a rigorous mathematical definition of what "correct" means ("formal specification"), and then showing that the code satisfies that definition ("formal verification"). You can see what this process looks like in practice at `Let's Prove Leftpad`_, which is another project I run.

You don't see formal verification a lot because it's *really, really hard.* There's just too many complicated things in general-purpose code. One way to get around this is to focus on verifying a much simpler domain, like abstract designs. That's what TLA+ does, making it easier to use at the cost of losting some power. 

I've got my design working, but how do I know my code is correct?
==================================================================

Ah, that's the difficult question! You can't 
Generate tests from sync

How does TLA+ compare to:
=========================

Unit Tests/Cucumber/TDD/PBT?
----------------------------

All of these act on *code*. You use them to check that you didn't make a mistake writing the code. TLA+, by contrast, acts on *designs*. You use it to check that your design actually does what you want it to do.

Checking designs has an obvious drawback: you can make a mistake implementing your design. But checking designs also has some big benefits: you can make a design faster and test it more thoroughly than you can its implementation. Take "our microservices architecture never submits the same payment twice, even if services go down". Testing that thoroughly would be a major undertaking. In TLA+ it'd be a couple-dozen lines.

Tradeoffs matter, and TLA+ is not "better than" testing. And if you're not already testing, TLA+ isn't the best investment. [#investment]_ But if you're already testing, then TLA+ is a fantastic addition to your toolbox.

SPARK/Idris/Dafny/Frama-C/F*?
-----------------------------

These are all about formally verifying code; you can see examples of what they all look like at `Let's Prove Leftpad`_. As mentioned, formally verifying code is extremely difficult, which is why TLA+ focuses instead on verifying designs.

(Comparing "testing code" to "verifying code" is a whole 'nother can of worms I can't really get into here. I wrote a very rough overview `here <https://www.hillelwayne.com/post/why-dont-people-use-formal-methods/>`__ but it's a few years out of date now.)



.. todo::

  Isabelle/Agda/Coq/Lean?
        ---

  These are all "theorem provers". They're 

  (TLA+ also has a theorem prover, called `TLAPS <tlaps>`.)

  `Let's Prove Leftpad`_


Alloy/Spin/Event-B/mCRL2?
-------------------------

Now we're getting into the hard stuff. These are all other formal specification languages with the same domain as TLA+: verifying abstract designs instead of working code. They're close enough for the subtle tradeoffs to matter. In my opinion, comparing any of these should be its own page, written by experts in both languages. 


P?
---

I gotta be honest, I haven't tried out P yet, so I have no idea how it compares to TLA+.

CTL*?
-----------

Dude if you know what CTL* is then you're clearly just messing with me

.. _Let's Prove Leftpad: https://github.com/hwayne/lets-prove-leftpad

.. [#investment] I've turned down potential clients for this reason.
