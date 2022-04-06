.. learntla documentation master file, created by
   sphinx-quickstart on Thu Jan 27 12:28:32 2022.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

.. todo:: 
  https://sphinx-tabs.readthedocs.io/en/latest/
  https://sphinx-book-theme.readthedocs.io/en/latest/

Welcome to learntla's documentation!
====================================

.. troubleshootinglist:: 

.. toctree::
   :maxdepth: 2
   :caption: Learning
   :hidden:

   intro/conceptual-overview.rst
   beginner/index
   intermediate/index



.. applying

.. 
  indexes and tables
  * :ref:`genindex`
  * :ref:`modindex`
  * :ref:`search`

::

  ---- MODULE test ----
  EXTENDS Integers, TLC, FiniteSets

  NULL == -1
  Servers == 1..3

  (*--algorithm threads
  variables 
    online = Servers;

  define
    Safety1 == [](\E s \in Servers: s \in online)
    Safety2 == \E s \in Servers: [](s \in online)
    Safety3 == Safety2 => Safety1
    P == ~[](online # {})
  end define;

  process orchestrator = "orchestrator"
  begin
    Change:
      while TRUE do
        with s \in Servers do
         either
            await s \notin online;
            online := online \cup {s};
          or
            await s \in online;
            online := online \ {s};
          end either;
        end with;
      end while;
  end process;

  end algorithm; *)
  \* BEGIN TRANSLATION - the hash of the PCal code: PCal-b8d567563e412065eeeae8a43be80d88
  VARIABLE online

  (* define statement *)
  Safety1 == [](\E s \in Servers: s \in online)
  Safety2 == \E s \in Servers: [](s \in online)
  Safety3 == Safety2 => Safety1
  P == ~[](online # {})


  vars == << online >>

  ProcSet == {"orchestrator"}

  Init == (* Global variables *)
          /\ online = Servers

  orchestrator == \E s \in Servers:
                    \/ /\ s \notin online
                       /\ online' = (online \cup {s})
                    \/ /\ s \in online
                       /\ online' = online \ {s}

  Next == orchestrator

  Spec == Init /\ [][Next]_vars

  \* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-66b50f3123a5f0163718aa90c18cc3a3

  ====


