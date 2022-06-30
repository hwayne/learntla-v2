:orphan:

++++++++++++++++++++++
Next Steps
++++++++++++++++++++++

Congratulations! You've reached the end of the core. You've now encountered all the core ideas of TLA+ and to use it to find bugs in designs.

That said, we're not quite done learning. There's a lot more to TLA+ than just the syntax and semantics. We haven't talked about model optimization, or design patterns, or how to use it as part of a development process, or how to run it from the command line. And the examples we used were all toy problems. What does modeling a real world spec look like?

In other words, how do you get *good* at TLA+?

First of all, there's the rest of the site to help you with that. The :doc:`topics section </topics/index>` is all about advanced TLA+ use: design considerations, `general tips <topic_tips>`, how to use `the tooling <topic_toolbox>` better, etc. And the :doc:`examples section</examples/index>` is a collection of operators and specifications for you to study.

.. note:: Both of these are a little, um, *aspirational* right now. There's only six topics written (of about 15), and right now the examples page is mostly just links to other examples on the internet. Check the `whatsnew` page for updates!

Beyond that, there's plenty of material around the web! You can check out the :doc:`other resources </reference/other-resources>` page for links.

Most important of all, though, is practice. To get better, you need to write specs. I'd strongly recommend starting by modeling systems you've worked with a while and know well. Write a high level specification of the architecture or one particular feature. Don't worry about being comprehensive, just focus on what you think you're capable of. 

At this stage, spec errors are more likely (but not *certainly*) due to your relative inexperience than indicative of real errors. That's why it's good to practice on systems you know well: it'll be easier to see what system assumption you missed or TLA+ mistake you made. Use that as part of your feedback loop and to develop your skills further.

(But don't rule out the possibility that it's a real, actual bug. That happens more often than you expect. Just don't jump to it as your first assumption.)

It's also okay to jump straight into speccing a greenfield system or debugging a known broken one. Ultimately, the best approach is whichever one motivates you most.

I hope you enjoyed learning TLA+! 
