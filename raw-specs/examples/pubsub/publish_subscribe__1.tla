target: specs/examples/pubsub/1/pubsub.tla
states:
  pubsub_1:
    constants: | 
      Servers "{s1, s2}" Clients "{c1, c2}" Topics "{t1, t2}" MaxMessages 4
    states: 23162
    distinct: 11864
!!!

LoadLocal !tlacli check % --const Servers "{s1, s2}" --const Clients "{c1, c2}" --const Topics "{t1, t2}" --const MaxMessages 4 --inv TypeInv
!!!
---- MODULE publish_subscribe__1 ----
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
          
            [c \in topics[t] |-> Append(client_queue[c], msg)] @@ client_queue
          
      end with;
      message_id := message_id + 1;
    end while;
end process;
end algorithm; *)
====
