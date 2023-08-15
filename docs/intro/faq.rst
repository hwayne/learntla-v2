##############
FAQ
##############

These are some of the questions I get regularly asked about TLA+. If you have one you'd like to see me answer, feel free to `ask me! <https://github.com/hwayne/learntla-v2/issues>`__

What's TLA+?
=================

TLA+ is a language for writing and checking "specifications", or system designs. Once you have your specification, you can then test the specification *directly* for bugs, even before you've written any code.

Who made it?
------------

`Leslie Lamport`_, who's also the man behind Byzantine fault tolerance, Paxos, and LaTeX.

Fun fact: LaTeX is short for "Lamport's TeX"!


What's PlusCal?
---------------

PlusCal is a :abbr:`DSL (Domain Specific Language)` that compiles down to TLA+. Most engineers find it an easier place to start than with pure TLA+, and it works great for a lot of specifications. The |core| starts off with PlusCal (`here's why <pluscal_vs_tla>`) but fully teaches TLA+ by the end. I wrote `topics <topics>` and `examples <examples>` for both TLA+ and PlusCal.

I've heard that TLA+ is a "formal method". What's that?
------------------------------------------------------------------

"Formal methods" is, very roughly, the field of computer science dedicated to writing correct programs. This is usually done by first writing a rigorous mathematical definition of what "correct" means ("formal specification"), and then showing that the code satisfies that definition ("formal verification"). You can see what this process looks like in practice at `Let's Prove Leftpad`_, which is another project I run.

You don't see formal verification a lot because it's *really, really hard.* There's just too many complicated things in general-purpose code. One way to get around this is to focus on verifying a much simpler domain, like abstract designs. That's what TLA+ does, making it easier to use at the cost of losing some power.

What does TLA stand for?
-------------------------

"Three Letter Acronym." [#tla]_


How does TLA+ test specifications?
==================================

There are a few different tools that work with TLA+, but the main one is called TLC, which does :term:`model checking`. That means it checker takes your specification and requirements, then checks *every possible behavior of the spec* against those requirements.

This gives much more thorough coverage than something like unit tests. Consider a system where three processes each do four sequential steps in parallel. There are 34,650 possible interleavings and 415,800 possible distinct states. TLC will check every single one.

What's the catch?
-----------------

The big one is that TLA+ tests *designs*, not *code*. There's no built-in way to generate code from designs or check designs against code. This is in part because high level-designs are so much denser than code: a 50 line design could take thousands of lines of code to implement.

(There are `some techniques <http://www.vldb.org/pvldb/vol13/p1346-davis.pdf>`__ that help keep them in sync. I plan to write them up as a `topic <topics>`.)

.. todo:: Write them as a topic

TLA+ also can't tell you if a design is good, practical, or even *implementable*, just whether it satisfies your requirements. It can help you in finding a good design, but you still need to put the work in. No tool can excuse us from being good engineers.

Does TLA+ actually find bugs?
-----------------------------

Yes! Here are just a few of the (public!) successful use cases:

* `Espark Learning`_, an edtech company with just ten engineers, used TLA+ to find complex bugs in a distributed app installer, saving weeks of development and hundreds of thousands in revenue per year. [#espark]_

* `Amazon Web Services`_ used TLA+ to model parts of S3 and DynamoDB, finding a 35-step bug that escaped all their tests and two code reviews.

* `CrowdStrike`_ found multiple failure cases over just five days of workshops.

TLA+ has also been used by Azure, MongoDB, Confluent, Elastic, and Cockroach Labs to find bugs.

.. Also: Auxon and that okta competitor

What's TLA+ good for?
=====================

TLA+ is great for modeling and finding bugs in concurrent and distributed systems. It's also good for modeling systems that span more than one codebase. Something like an `AWS Step Function <https://aws.amazon.com/step-functions/?step-functions.sort-by=item.additionalFields.postDateTime&step-functions.sort-order=desc>`__ involves multiple programs, services, and even human actors working together. All of these can be incorporated into a single system design and checked for errors.

What's TLA+ bad for?
====================

Like any tool, TLA+ has limitations. Aside from the obvious one (can't test your code), there are some TLA+ weak spots:

- Numerical code. TLA+ supports integers but not decimals or floating-point.
- String manipulation. You can represent strings as a sequence of characters for basic manipulation, but it gets awkward.
- Probabilistic properties. You can say "X definitely happens" or "X never happens", but not "X happens at least 90% of the time". There are `special tools`_ for checking those kinds of properties.
- Reachability properties. You can't say "it's always *possible* for X to eventually happen, even if it doesn't *have* to happen."
- Realtime properties, like "If Y happens, X has to happen within five real actual seconds".

There's also some limitations to the current tooling. There's not yet official features for interactive spec exploration or visualization.

Do I need a strong math background to use TLA+?
===============================================

TLA+ does use a bit of math that's not often used in regular programming, but it's all learnable as you go. The |core| gradually explains it as you go along.

(If you want to know what to expect, the new math concepts are the boolean statement "X implies Y" and the set quantifiers "forall/some x in set".)


Does using TLA+ mean I don't have to write tests?
=================================================

Absolutely not. It only verifies the design is correct, not that the code is correct. Write your tests.



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

Now we're getting into the hard stuff. These are all other formal specification languages with the same domain as TLA+: verifying abstract designs instead of working code. They're close enough for the subtle tradeoffs to matter. In my opinion, any comparisons of these tools needs to be be its own page, written by experts in both languages.


P?
---

I gotta be honest, I haven't tried out P yet, so I have no idea how it compares to TLA+.

CTL*?
-----------

Dude if you know what CTL* is then you're clearly just messing with me

.. _Let's Prove Leftpad: https://github.com/hwayne/lets-prove-leftpad


.. _Espark Learning: https://medium.com/espark-engineering-blog/formal-methods-in-practice-8f20d72bce4f

.. [#TLA] Okay okay, it's actually "Temporal Logic of Actions". TLA+ is designed around the "core" of TLA. TLA+ users are a little shy about sharing the acronym because it intimidates beginners who'd otherwise have little trouble learning TLA+.

.. [#espark] Disclaimer, I worked on this project. In fact it was how I started using TLA+!

.. [#investment] I've turned down potential clients for this reason.


.. _Amazon Web Services: https://cacm.acm.org/magazines/2015/4/184701-how-amazon-web-services-uses-formal-methods/fulltext

.. _special tools: https://www.prismmodelchecker.org/


.. _Leslie Lamport: https://en.wikipedia.org/wiki/Leslie_Lamport

.. _CrowdStrike: https://www.youtube.com/watch?v=QKCG3tz4mOU
