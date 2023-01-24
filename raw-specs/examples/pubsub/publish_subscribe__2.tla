target: specs/examples/pubsub/2/pubsub.tla
!!!
!tlacli translate %
LoadLocal !tlacli check % --const Servers "{s1, s2}" --const Clients "{c1, c2}" --const Topics "{t1, t2}" --const MaxMessages 4 --inv TypeInv
!!!

---- MODULE publish_subscribe__2 ----
EXTENDS TLC, Sequences, Integers
CONSTANT Servers, Clients, Topics, MaxMessages 

------
Range(f) == {f[x]: x \in DOMAIN f}
set ++ x == set \union {x}
set -- x == set \ {x}
------

MessageType ==
  [id: Nat, server: Servers]

(*--algorithm pubsub
variables 
  message_id = 1;
  messages = 1;
  client_queue = [c \in Clients |-> <<>>];
  topics = [t \in Topics |-> {}];

define
  TypeInv ==
    /\ message_id \in Nat
    /\ client_queue \in [Clients -> Seq(MessageType)]
    /\ topics \in [Topics -> SUBSET Clients]
end define


process client \in Clients
begin
  Client:
    either
      \* Subscribe
      with t \in Topics do
        topics[t] := topics[t] ++ self;
      end with;
    or
      \* Unsub
      with t \in Topics do
        topics[t] := topics[t] -- self;
      end with;
    or
      \* Read
      await client_queue[self] # <<>>;
      client_queue[self] := Tail(client_queue[self])
    end either;
end process;

process server \in Servers
begin
  Server:
    while message_id <= MaxMessages do
      with 
        t \in Topics, 
        msg = [id |-> message_id, server |-> self] 
      do
        client_queue :=
          
          LET cq == client_queue IN
            [c \in topics[t] |-> Append(cq[c], msg)] @@ cq
          
      end with;
      message_id := message_id + 1;
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a49bbf654f93051e1d92dcd9bb63ee91
VARIABLES message_id, messages, client_queue, topics, pc

(* define statement *)
TypeInv ==
  /\ message_id \in Nat
  /\ client_queue \in [Clients -> Seq(MessageType)]
  /\ topics \in [Topics -> SUBSET Clients]


vars == << message_id, messages, client_queue, topics, pc >>

ProcSet == (Clients) \cup (Servers)

Init == (* Global variables *)
        /\ message_id = 1
        /\ messages = 1
        /\ client_queue = [c \in Clients |-> <<>>]
        /\ topics = [t \in Topics |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Client"
                                        [] self \in Servers -> "Server"]

Client(self) == /\ pc[self] = "Client"
                /\ \/ /\ \E t \in Topics:
                           topics' = [topics EXCEPT ![t] = topics[t] ++ self]
                      /\ UNCHANGED client_queue
                   \/ /\ \E t \in Topics:
                           topics' = [topics EXCEPT ![t] = topics[t] -- self]
                      /\ UNCHANGED client_queue
                   \/ /\ client_queue[self] # <<>>
                      /\ client_queue' = [client_queue EXCEPT ![self] = Tail(client_queue[self])]
                      /\ UNCHANGED topics
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << message_id, messages >>

client(self) == Client(self)

Server(self) == /\ pc[self] = "Server"
                /\ IF message_id <= MaxMessages
                      THEN /\ \E t \in Topics:
                                LET msg == [id |-> message_id, server |-> self] IN
                                  client_queue' = (LET cq == client_queue IN
                                                     [c \in topics[t] |-> Append(cq[c], msg)] @@ cq)
                           /\ message_id' = message_id + 1
                           /\ pc' = [pc EXCEPT ![self] = "Server"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED << message_id, client_queue >>
                /\ UNCHANGED << messages, topics >>

server(self) == Server(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: client(self))
           \/ (\E self \in Servers: server(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-63415410e51020178a29f84fa9efb518
====
