.. _example_goroutines:

##########
Goroutines
##########

.. note:: This example was originally published on `my blog <https://hillelwayne.com/post/tla-golang/>`__ and is adapted here with minor revisions.

In `Even in Go, concurrency is still not
easy <https://utcc.utoronto.ca/~cks/space/blog/programming/GoConcurrencyStillNotEasy>`__, Chris Siebenmann gives an example of Go code which deadlocks:

.. code-block:: go
  :linenos:

    func FindAll() []P { //P = process data
       pss, err := ps.Processes()
       [...]
       found := make(chan P)
       limitCh := make(chan struct{}, concurrencyProcesses)
    
       for _, pr := range pss {
          limitCh <- struct{}{}
          pr := pr
          go func() {
             defer func() { <-limitCh }()
             [... get a P with some error checking ...]
             found <- P
          }()
       }
       [...]
    
       var results []P
       for p := range found {
          results = append(results, p)
       }
       return results
    }

In his words:

.. rst-class:: quote
..

   The bug is that the goroutines only receive from limitCh to release their token after sending their result to the unbuffered found channel, while the main code only starts receiving from found after running through the entire loop, and the main code takes the token in the loop and blocks if no tokens are available.

This is a good example of directly verifying code with a TLA+ spec, instead of verifying just a design.

Planning Ahead
~~~~~~~~~~~~~~

It's good to start with some upfront thinking of how we are going to
approach this problem. There's two parts to formally specifying
something: describing the system and describing the properties of the
system. In this case we can ignore the second part, since we're only
looking for deadlocks. It would be good modeling practice to add sanity
check properties, like type invariants, but they are not strictly
necessary.

First, we want to pick whether we'll model in TLA+ or PlusCal. Since the Go code is highly sequential, I will use PlusCal. This will cause a bit of impedance
mismatch down the road for unbuffered channels but overall it's a net
benefit. 

There are three "complex bits" to Chris's code sample: ``go``,
``defer``, and the nature of Go channels. ``defer`` runs cleanup code
when a goroutine is finished running. For now we'll represent this by
moving the deferred code to its own label, but we could also use a
PlusCal procedure to be more accurate. ``go`` spawns a new goroutine.
Since PlusCal requires us to define all of our processes in advance, we
can't "spawn" a new goroutine. What we can do instead is define each
process but prevent them from running. Then we add a flag that says
whether or not the goroutine was initialized in the behavior yet. It
would look something like this:

.. code:: tla

   variables
     initialized = [w \in Routines |-> FALSE];

   \* ...

   process goroutine \in Routines
   begin
     Work:
       await initialized[self];
   \* ...

So each goroutine ``awaits`` being initialized by the main process
before it does anything. This is how we can emulate spawning new
processes.

That leaves the channels, which are the most complicated part to
specify. There are two kinds of Go channels: buffered and unbuffered.
Sends to a buffered channel are blocked if the channel is full. Receives
from a buffered channel are blocked if the channel is empty. Both of
these are representable with PlusCal macros:

.. code:: tla

   macro send_buffered(chan) begin
     await channels[chan] < buffered[chan];
     channels[chan] := channels[chan] + 1;
   end macro;

   macro receive_buffered(chan) begin
     await channels[chan] > 0;
     channels[chan] := channels[chan] - 1;
   end macro;

.. For the purposes of pedagogy I'm not modeling what we actually read or write. This is good practice when writing real-world specs too: write the simplest specification that usefully captures behavior and iteratively add detail to that.

That covers buffered channels. Unbuffered channels, by contrast, always
block unless there is *both* a sender and receiver. In pure TLA+ this
wouldn't be too tricky to specify, but PlusCal assumes each step of the
behavior is one process doing one thing. Unbuffered channels can't be
represented natively without adding some annoying bookkeeping, as we
need to have one process block "first". For that we can use a `procedure`.

So now that we know a rough approach and what the pain points are likely
to be, let's write the spec.

The spec
~~~~~~~~

First the breakdown, then the whole spec.

.. code:: tla

   ---- MODULE channels ----
   EXTENDS Integers, TLC, Sequences

   CONSTANTS NumRoutines, NumTokens
   Routines == 1..NumRoutines

   (* --algorithm channels

   variables
     channels = [tokens |-> 0, found |-> {}];
     buffered = [tokens |-> NumTokens];
     initialized = [w \in Routines |-> FALSE];

``channels`` is the current contents of each channel. For buffered
channels, we treat their contents as a single number and store the
maximum capacity in a separate ``buffered`` variable. For unbuffered
channels, we instead store the set of senders waiting for a receiver.
``initialized`` is for emulating goroutines.

.. code:: tla

   macro go(routine) begin
     initialized[routine] := TRUE;
   end macro

An extra macro I added to more closely match the Go syntax.

.. code:: tla

   macro write_buffered(chan) begin
     await channels[chan] < buffered[chan];
     channels[chan] := channels[chan] + 1;
   end macro;

   macro receive_channel(chan) begin
     if chan \in DOMAIN buffered then
       await channels[chan] > 0;
       channels[chan] := channels[chan] - 1;
     else
       await channels[chan] # {};
       with w \in channels[chan] do
         channels[chan] := channels[chan] \ {w}
       end with;
     end if;
   end macro;

This is a change from our old ``read_buffered`` because it handles both
buffered and unbuffered channels. Buffered channels work as expected.
For unbuffered channels, we wait for the set of blocked writers to be
nonempty and nondeterministically declare that we read from one of
them. [1]_

.. code:: tla

   procedure write_unbuffered(chan) begin
     DeclareSend:
       channels[chan] := channels[chan] \union {self};
     Send:
       await self \notin channels[chan];
       return;
   end procedure

To model unbuffered channels we can either put state on senders or put
state on receivers. I opted to place it on the sender because Go permits
`reading from multiple unbuffered channels at
once <https://golang.org/ref/spec#Select_statements>`__. [2]_ In two
separate temporal steps we 1) add the process to the set of channel
senders and 2) wait to be removed from that set by a receiver.

.. code:: tla

   process goroutine \in Routines
   begin
     A:
       await initialized[self];
       call write_unbuffered("found");
     B:
       receive_channel("tokens");
   end process;

Our goroutine process is a straightforward translation of the Go code.
First we wait for the goroutine to be initialized, corresponding to line
10. Then we write to the ``found`` channel (line 13). If I was trying to
be more faithful I would write special ``defer`` semantics, but for this
I'm happy to just stick it on a label at the end of the process.

.. code:: tla

   process main = 0
   variables i = 1;
   begin
     Main:
       while i <= NumRoutines do
         write_buffered("tokens");
         go(i);
         i := i + 1;
       end while;
     Get:
       while i > 1 do
         i := i - 1;
         receive_channel("found");
       end while;
   end process;

   end algorithm; *)

Our emulation uses one token to initialize each goroutine.
Since ``write_channel`` has an ``await`` in it, it will block if there
are more goroutines than tokens. It will then stay blocked until a
goroutine releases a token. [3]_ Final spec:


.. code:: tla

   ---- MODULE channels ----
   EXTENDS Integers, TLC, Sequences

   CONSTANTS NumRoutines, NumTokens

   Routines == 1..NumRoutines

   (* --algorithm channels

   variables
     channels = [limitCh |-> 0, found |-> {}];
     buffered = [limitCh |-> NumTokens];
     initialized = [w \in Routines |-> FALSE];


   macro send_buffered(chan) begin
     await channels[chan] < buffered[chan];
     channels[chan] := channels[chan] + 1;
   end macro;

   macro receive_channel(chan) begin
     if chan \in DOMAIN buffered then
       await channels[chan] > 0;
       channels[chan] := channels[chan] - 1;
     else
       await channels[chan] # {};
       with w \in channels[chan] do
         channels[chan] := channels[chan] \ {w}
       end with;
     end if;
   end macro;

   macro go(routine) begin
     initialized[routine] := TRUE;
   end macro

   procedure send_unbuffered(chan) begin
     DeclareSend:
       channels[chan] := channels[chan] \union {self};
     Send:
       await self \notin channels[chan];
       return;
   end procedure

   process goroutine \in Routines
   begin
     A:
       await initialized[self];
       call send_unbuffered("found");
     B:
       receive_channel("limitCh");
   end process;

   process main = 0
   variables i = 1;
   begin
     Main:
       while i <= NumRoutines do
         send_buffered("limitCh");
         go(i);
         i := i + 1;
       end while;
     Get:
       while i > 1 do
         i := i - 1;
         receive_channel("found");
       end while;
   end process;

   end algorithm; *)
   ====


Now that we have a full spec, we can use the model checker, TLC, to see
if it satisfies any properties. We didn't specify any, but TLC will
check for deadlocks by default. 

Finding Deadlocks
~~~~~~~~~~~~~~~~~

To make this deadlock, I checked it with ``NumRoutines <- 3, NumTokens <- 2``. {{TODO state space}}. Unsurprisingly, this deadlocks: [5]_

.. code-block:: none

   State 1: <Initial predicate>
   /\ buffered = [limitCh |-> 2]
   /\ channels = [limitCh |-> 0, found |-> {}]
   /\ i = 1
   /\ pc = (0 :> "Main" @@ 1 :> "A" @@ 2 :> "A" @@ 3 :> "A")
   /\ initialized = <<FALSE, FALSE, FALSE>>

   State 2: <Main line 128, col 9 to line 137, col 48 of module base>
   /\ buffered = [limitCh |-> 2]
   /\ channels = [limitCh |-> 1, found |-> {}]
   /\ i = 2
   /\ pc = (0 :> "Main" @@ 1 :> "A" @@ 2 :> "A" @@ 3 :> "A")
   /\ initialized = <<TRUE, FALSE, FALSE>>

   State 3: <Main line 128, col 9 to line 137, col 48 of module base>
   /\ buffered = [limitCh |-> 2]
   /\ channels = [limitCh |-> 2, found |-> {}]
   /\ i = 3
   /\ pc = (0 :> "Main" @@ 1 :> "A" @@ 2 :> "A" @@ 3 :> "A")
   /\ initialized = <<TRUE, TRUE, FALSE>>

   State 4: <A line 106, col 12 to line 114, col 64 of module base>
   /\ buffered = [limitCh |-> 2]
   /\ channels = [limitCh |-> 2, found |-> {}]
   /\ i = 3
   /\ pc = (0 :> "Main" @@ 1 :> "A" @@ 2 :> "DeclareSend" @@ 3 :> "A")
   /\ initialized = <<TRUE, TRUE, FALSE>>

   State 5: <A line 106, col 12 to line 114, col 64 of module base>
   /\ buffered = [limitCh |-> 2]
   /\ channels = [limitCh |-> 2, found |-> {}]
   /\ i = 3
   /\ pc = (0 :> "Main" @@ 1 :> "DeclareSend" @@ 2 :> "DeclareSend" @@ 3 :> "A")
   /\ initialized = <<TRUE, TRUE, FALSE>>

   State 6: <DeclareSend line 92, col 22 to line 95, col 77 of module base>
   /\ buffered = [limitCh |-> 2]
   /\ channels = [limitCh |-> 2, found |-> {1}]
   /\ i = 3
   /\ pc = (0 :> "Main" @@ 1 :> "Send" @@ 2 :> "DeclareSend" @@ 3 :> "A")
   /\ initialized = <<TRUE, TRUE, FALSE>>

   State 7: <DeclareSend line 92, col 22 to line 95, col 77 of module base>
   /\ buffered = [limitCh |-> 2]
   /\ channels = [limitCh |-> 2, found |-> {1, 2}]
   /\ i = 3
   /\ pc = (0 :> "Main" @@ 1 :> "Send" @@ 2 :> "Send" @@ 3 :> "A")
   /\ initialized = <<TRUE, TRUE, FALSE>>

It's the same issue that Chris had. The goroutines can only return their
tokens if there is a receiver on the ``found`` channel, the only
receiver of that channel is ``main``, ``main`` only reads after it
initializes all the goroutines, and ``main`` will block if there are
more goroutines than tokens. The goroutines can't return tokens until
all goroutines are initialized, and main can't initialize all goroutines
until some goroutines have returned their tokens.

Fixing This
~~~~~~~~~~~

Chris suggests three possible ways of fixing this. We can test each of
the three by modifying our spec:

.. rst-class:: quote
..

   If the goroutines took the token by sending to ``limitCh`` instead of
   the main for loop doing it, the bug would not exist;

.. code:: diff

   process goroutine \in Routines
   begin
     A:
       await initialized[self];
   +   write_buffered("limitCh");

   \* ...

       while i <= NumRoutines do
   -     write_buffered("limitCh");
         initialized[i] := TRUE;
         i := i + 1;
       end while;

This passes model checking.

.. rst-class:: quote
..

   If the goroutines received from ``limitCh`` to release their token
   before sending to ``found``, it wouldn't exist (but because of error
   handling, it's simpler and more reliable to do the receive in a
   defer).

.. code:: diff

   process goroutine \in Routines
   begin
    A:
      await initialized[self];
   +   receive_channel("limitCh");
   -   call write_unbuffered("found");
    B:
   -   receive_channel("limitCh");
   +   call write_unbuffered("found");
   end process;

This passes model checking.

.. rst-class:: quote
..

   And if the entire for loop was in an additional goroutine…

This one's a little more complicated. We create a new process for the
loop and add its identifier to ``initialized``. I'll use ``-1`` to
represent the for-loop.

.. code:: tla

   initialized = [w \in Routines \union {-1} |-> FALSE];

   \* After goroutines

   process for_loop = -1
   variables i = 1;
   begin
     Loop:
       while i <= NumRoutines do
         write_buffered("limitCh");
         go(i);
         i := i + 1;
       end while;
   end process;

Then we modify ``main`` to initialize this instead of doing the loop
itself:

.. code:: tla

   process main = 0
   variables i = NumRoutines;
   begin
     Main:
       go(-1);
     Get:
       while i > 0 do
         i := i - 1;
         receive_channel("found");
       end while;
   end process;

This passes model checking.

Discussion
----------

Ultimately we wrote about 75 lines of specification to test 20 lines of
Go code. Over half the spec is channel logic which we can now reuse in
other specs. Discounting those puts us a little closer, though I'll
admit that a real TLA+ spec would be a lot longer because you'd be
writing a lot more sanity checking properties. Nonetheless, writing the
TLA+ version wouldn't be significantly more effort than writing the
original version and could save you net time if it caught the deadlock
before production.

.. todo:: TLA+ version

.. [1]
   ``with`` blocks if the set is empty, making the ``await`` statement
   above it redundant. I added it purely for clarity.

.. [2]
   You can also use a ``select`` to send to multiple channels, but I
   think that's less common? This is where being able to write a raw
   TLA+ action could be really helpful.

.. [3]
   ``Get`` is an inaccurate representation of how channel receives in a
   ``range`` work: it should loop until the channel is closed. I left
   that out here because the rest of the spec doesn't depend on closing
   channels and I didn't want to add extra complexity to this example.

.. [5]
   I removed the ``stack`` and ``chan`` variables from the trace to make
   it a little clearer.
