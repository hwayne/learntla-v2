:orphan:

##############
Intro FAQ
##############

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

What can't TLA+ do?
====================

Test code directly
numbers
String manipulation
Probabilistic properties
Good layouts


I've got my design working, but how do I know my code is correct?
==================================================================

Can't easily
Generate tests from sync

How does it compare to ${OTHER_LANGUAGE}
========================================

I haven't written this yet but plan to.

How does it compare to testing?

How does it compare to property-based testing?
