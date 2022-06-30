.. _topic_state_machines:

########################
Finite State Machines
########################

The dirty secret of formal methods is that the only way we know to scale it up is to use state machines. So we might as well learn how to write state machines in TLA+!

.. note:: I want to write a formal introduction, but in the meantime, `here's <http://howtomakeanrpg.com/a/state-machines.html>`__ a good introduction to state machines. 

A Simple State Machine
======================

I have a lamp in my bedroom that's controlled by both a lamp switch and an wall switch. Both switches have to be on in order for the lamp to be one. The state machine looks like this:

.. graphviz:: 

  digraph StateMachine {
    {rank=same; WallOff; LampOff}
    {rank=max; On}
    {rank=source; BothOff}
    {BothOff On} -> WallOff[label="lamp switch"];
    {BothOff On} -> LampOff[label="wall switch"];
    WallOff -> BothOff[label="lamp switch"];
    WallOff -> On[label="wall switch"];
    LampOff -> On[label="lamp switch"];
    LampOff -> BothOff[label="wall switch"];
  }

A few things to notice:

- The transitions are nondeterministic. From :math:`BothOff`, I can either flip the wall switch or the lamp switch.
- There's no transitions between :math:`BothOff` and :math:`On`, I have to flip the switches one at a time.
- For the same reason, there's no way to get between :math:`WallOff` and :math:`LampOff`.

In PlusCal, we can model a state machine by placing `await` statements inside an `either` block. If the ``await`` is false the branch is blocked off, but the other branches are still available, preserving nondeterminism.

.. spec:: topics/state_machines/lamp/pluscal/state_machine.tla
  :ss: sm_simple

Now that's a bit long, as we need one transition per state machine. We could simplify this with a macro:

::

  macro transition(from, to) begin
    await state = from;
    state := to;
  end macro;

Or even

::

  macro transition(from, set_to) begin
    await state = from;
    with to \in set_to begin
      state := to;
    end with;
  end macro;

In my opinion, things look a little cleaner if we just do it all in TLA+. 


.. spec:: topics/state_machines/lamp/tla/state_machine.tla
  :ss: sm_simple

For this reason I'm going to stick with TLA+ going forward. You can still do state machines in PlusCal, it's just that more complicated stuff is messier.


Hierarchical State Machines
=============================

What's better than a state machine? A *nested* state machine.

Also known as `Harel Statecharts <https://www.cs.scranton.edu/~mccloske/courses/se507/harel_Statecharts.pdf>`__, hierarchical state machines allow states inside of other states. If state P' is inside of state P, then P' can take any transitions that P can take. A simple example is the UI of a web app. You can log on or off, and when logged in you start in a homepage and can move to any secondary page. To make things interesting we'll say one of the secondary pages also as subpages.


.. digraph:: hsl

  compound=true;

  LogOut
  
    LogOut -> Main;
  subgraph cluster_app {
    label="Logged In";
    Main -> Settings [dir=both];
    Main -> Report1[ltail="cluster_app"];
    Report1 -> {Main Settings}[ltail="cluster_reports"];
    
    subgraph cluster_reports {
      label=Reports
      Report1;
      Report2;
      Report1 -> Report2[dir=both];
    }
  }
  Main -> LogOut[ltail="cluster_app"];

.. note:: There's a few different flavors of HSM. For this one, I'm following three restrictions:

  1. Transitions can start from any state, but must end in a "leaf" state. You can't be in ``LoggedIn`` or ``Reports``, you have to be in ``Main`` or ``Report1``.
  2. A state can't have two different parent states.
  3. No state cycles.

To model the hierarchical states, I want to be able to write ``Trans("LoggedIn", "Logout")`` and have that include every state of the app: Main, Settings, Report1, and Report2. So we need an ``In(state1, state2)`` that's recursive. Then ``Trans`` becomes

::

  Trans(from, to) ==
    /\ In(state, from) \* Recursive!
    /\ state' = to

To represent the state hierarchy, we can go either top-down (a function from states to the set of child states) or bottom-up (a function from states to their parent states). Each has relative tradeoffs:

#. *Top-down*: Function domain guaranteed to be all states. Can accidentally give two states the same child.
#. *Bottom-up*: Impossible for a state to have two parents. Worse ergonomics on checking ``In``, as not all states will be in the function's domain. Harder to check if a state doesn't have children.

Ah heck, let's implement both and check they're equivalent.

.. spec:: topics/state_machines/reports/1/reports.tla
  :ss: sm_reports

