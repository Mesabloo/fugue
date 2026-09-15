------------------------- MODULE ReplicatedKVS -------------------------------
\* Distributed PlusCal translation of the classic MPCal replicated-KV tutorial example
\* (archetypes AReplica / Get / Put / Disconnect / ClockUpdate). This dialect has no global
\* variables, so every variable that was global in the MPCal source had to be resolved to
\* exactly one of: (a) a single process's local state, or (b) a channel.
\*
\* The one non-mechanical step: the MPCal source modeled each client's four operations
\* (Get-loop, Put-loop, Disconnect, ClockUpdate-loop) as four *separate* PlusCal processes,
\* tied together only by sharing one slot of the global `clocks` array through identifier
\* arithmetic (`self - NUM_CLIENTS * ORDER`). That only type-checks in MPCal because its
\* compiler assumes those four processes end up as goroutines of the same OS process, so
\* sharing a Go variable is free. This dialect has no such backdoor: four distinct
\* `process` declarations are four distinct addresses with no shared memory. So instead
\* the four operations become four thread-blocks of a single `process (c \in ClientSet)`
\* (the same multi-thread-per-process shape `TwoPhaseCommit.tla`'s coordinator uses) --
\* exactly matching how one would actually deploy this (one client node running four
\* concurrent goroutines that share the node's own Lamport clock). Scratch variables that
\* were archetype-local in MPCal (each archetype got its own fresh `i`, `j`, `msg`, ...) are
\* renamed per-thread here since all four threads of one process share one variable
\* namespace.
\*
\* Minor fix along the way: MPCal's stability tie-break used `nextClient := NUM_NODES + 1`
\* as an out-of-domain sentinel guaranteed larger than any real client id, then compared
\* with plain `<`. `Address` here is opaque (no arithmetic, no max element) but does carry
\* a fixed-but-unspecified total order (`\prec`, from `Fugue`). The sentinel trick turns out
\* to be unnecessary: `nextClient`'s initial value is only ever read as the second operand
\* of a disjunction whose first operand (`timestamp < lowestPending`) is already TRUE the
\* first time any candidate is chosen, so any well-typed initial Address works -- `self` is
\* used here -- and every later comparison is between two genuine candidate clients, where
\* `\prec` replaces `<` directly.
\*
\* `out`/`outside` in the MPCal source was explicitly "abstracted" -- a single global scalar
\* every client's Get/Put clobbered, used only so TLC has something to inspect, never read
\* by the protocol itself. Kept as ordinary per-client local state here (each client remembers
\* its own last result) rather than invented as a channel, since nothing in the protocol
\* depends on it being shared.
EXTENDS Integers, Sequences, FiniteSets, TLC, Fugue 

CONSTANTS
    \* @type: Set(Address);
    ReplicaSet,    
    \* @type: Set(Address);
    ClientSet,
    \* upper bound on a client's Lamport clock before it disconnects -- 100 in production,
    \* kept tiny for TLC (see Paxos.tla's MaxRound for the same pattern)
    \* @type: Int;
    MaxClock

ASSUME MaxClock > 0

\* @type: Str;
DisconnectMessage == "disconnect"
\* @type: Str;
GetMessage == "get"
\* @type: Str;
PutMessage == "put"
\* @type: Str;
NullMessage == "null"

\* @type: Str;
GetResponse == "get-"
\* @type: Str;
PutResponse == "put-"

\* @type: Str;
GetKey == "GET"
\* @type: Str;
PutKey == "PUT"
\* @type: Set(Str);
KeySpace == { GetKey, PutKey }

\* @type: Str;
PutValue == "value1"
\* @type: Str;
NoValue == "none"
\* @type: Str;
OkValue == "ok"

\* named so its type is fixed at the declaration rather than re-inferred where it's used --
\* an empty sequence literal used directly as a function-comprehension body doesn't pick up
\* the comprehension's expected codomain type.
\* @type: Seq({op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address});
EmptyRequestQueue == <<>>

(* PlusCal options (-distpcal) *)
(*--algorithm ReplicatedKVS {
    fifos
        \* @type: Address -> Channel({op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address});
        replicasNetwork[ReplicaSet],
        \* @type: Address -> Channel({type: Str, result: Str});
        clientMailboxes[ClientSet];

    \* @mailbox: replicasNetwork[self];
    process (r \in ReplicaSet)
        variables
            \* clients this replica still considers connected
            \* @type: Set(Address);
            liveClients = ClientSet,
            \* per-client queue of not-yet-stable requests
            \* @type: Address -> Seq({op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address});
            pendingRequests = [c \in ClientSet |-> EmptyRequestQueue],
            \* @type: Seq({op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address});
            stableMessages = <<>>,
            \* @type: Int;
            i = 0,
            \* @type: {op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address};
            firstPending = [op |-> NullMessage, key |-> NoValue, value |-> NoValue, client |-> self, timestamp |-> 0, reply_to |-> self],
            \* @type: Int;
            timestamp = 0,
            \* @type: Address;
            nextClient = self,
            \* @type: Int;
            lowestPending = 0,
            \* @type: Bool;
            chooseMessage = FALSE,
            \* last logical clock seen from each client
            \* @type: Address -> Int;
            currentClocks = [c \in ClientSet |-> 0],
            \* @type: Int;
            minClock = 0,
            \* @type: Bool;
            continue = FALSE,
            \* @type: Set(Address);
            pendingClients = {},
            \* @type: Set(Address);
            clientsIter = {},
            \* @type: {op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address};
            msg = [op |-> NullMessage, key |-> NoValue, value |-> NoValue, client |-> self, timestamp |-> 0, reply_to |-> self],
            \* this replica's own copy of the database -- private, never shared
            \* @type: Str -> Str;
            kv = [k \in KeySpace |-> NoValue];
    {
    replicaLoop:
        while (TRUE) {
            stableMessages := <<>>;
            continue := TRUE;

        receiveClientRequest:
            receive(replicasNetwork[self], msg);

            either {
                await msg.op = DisconnectMessage;
                liveClients := liveClients \ {msg.client};
            } or {
                await msg.op = GetMessage;
                assert(msg.client \in liveClients);
                currentClocks[msg.client] := msg.timestamp;
                pendingRequests[msg.client] := Append(pendingRequests[msg.client], msg);
            } or {
                await msg.op = PutMessage;
                currentClocks[msg.client] := msg.timestamp;
                pendingRequests[msg.client] := Append(pendingRequests[msg.client], msg);
            } or {
                await msg.op = NullMessage;
                currentClocks[msg.client] := msg.timestamp;
            };

        findStableRequestsLoop:
            while (continue) {
                pendingClients := {c \in liveClients : Len(pendingRequests[c]) > 0};

                \* dummy initial candidate -- see file header note on `\prec`
                nextClient := self;

                clientsIter := liveClients;
                i := 0;
                minClock := 0;

            findMinClock:
                while (i < Cardinality(clientsIter)) {
                    with (client \in clientsIter) {
                        if (minClock = 0 \/ currentClocks[client] < minClock) {
                            minClock := currentClocks[client];
                        };
                        clientsIter := clientsIter \ {client};
                    }
                };

                lowestPending := minClock + 1;
                i := 0;

            findMinClient:
                while (i < Cardinality(pendingClients)) {
                    with (client \in pendingClients) {
                        firstPending := Head(pendingRequests[client]);
                        assert(firstPending.op = GetMessage \/ firstPending.op = PutMessage);
                        timestamp := firstPending.timestamp;

                        if (timestamp < minClock) {
                            chooseMessage := (timestamp < lowestPending) \/ ((timestamp = lowestPending) /\ (client \prec nextClient));
                            if (chooseMessage) {
                                nextClient := client;
                                lowestPending := timestamp;
                            }
                        };

                        pendingClients := pendingClients \ {client};
                    }
                };

            addStableMessage:
                if (lowestPending < minClock) {
                    msg := Head(pendingRequests[nextClient]);
                    pendingRequests[nextClient] := Tail(pendingRequests[nextClient]);
                    stableMessages := Append(stableMessages, msg);
                } else {
                    continue := FALSE;
                }
            };

            i := 1;

        respondPendingRequestsLoop:
            while (i <= Len(stableMessages)) {
                msg := stableMessages[i];
                i := i + 1;

            respondStable:
                either {
                    await msg.op = GetMessage;
                    send(clientMailboxes[msg.reply_to], [type |-> GetResponse, result |-> kv[msg.key]]);
                } or {
                    await msg.op = PutMessage;
                    kv[msg.key] := msg.value;
                    send(clientMailboxes[msg.reply_to], [type |-> PutResponse, result |-> OkValue]);
                }
            }
        }
    }

    \* @mailbox: clientMailboxes[self];
    process (c \in ClientSet)
        variables
            \* shared by all four threads below -- this is the client's one Lamport clock
            \* @type: Int;
            clock = 0,
            \* last result observed by this client; bookkeeping only, protocol never reads it
            \* @type: Str;
            outside = "",
            \* getLoop and putLoop both receive off the one shared clientMailboxes[self]
            \* queue with no tag telling one reply from the other, so at most one of the
            \* two may have a request outstanding at a time -- this flag is that mutex.
            \* @type: Bool;
            awaitingReply = FALSE,

            \* getReply/putResponse never overlap -- awaitingReply mutexes the shared
            \* clientMailboxes[self] receive between the Get and Put threads -- so both
            \* reuse this one slot instead of two identically-shaped variables.
            \* @type: {type: Str, result: Str};
            resp = [type |-> "", result |-> ""],

            \* -- Put thread --
            \* @type: Int;
            putI = 0;
    {
    getLoop:
        while (clock # -1) {
        getRequest:
            if (clock # -1) {
                await ~awaitingReply;
                awaitingReply := TRUE;
                clock := clock + 1;
                with (dst \in ReplicaSet) {
                    send(replicasNetwork[dst], [op |-> GetMessage, key |-> GetKey, value |-> NoValue, client |-> self, timestamp |-> clock, reply_to |-> self]);
                };

            getReply:
                if (clock # -1) {
                    receive(clientMailboxes[self], resp);
                    assert(resp.type = GetResponse);
                    outside := resp.result;
                };
                awaitingReply := FALSE;
            }
        }
    }
    {
    putLoop:
        while (clock # -1) {
        putRequest:
            if (clock # -1) {
                await ~awaitingReply;
                awaitingReply := TRUE;
                clock := clock + 1;
                putI := 0;
                multicast(replicasNetwork, [dst \in ReplicaSet |-> [op |-> PutMessage, key |-> PutKey, value |-> PutValue, client |-> self, timestamp |-> clock, reply_to |-> self]]);

            putResponse:
                while (putI < Cardinality(ReplicaSet)) {
                    if (clock = -1) {
                        awaitingReply := FALSE;
                        goto putLoop;
                    } else {
                        receive(clientMailboxes[self], resp);
                        assert(resp.type = PutResponse);
                        putI := putI + 1;
                    }
                };

            putComplete:
                outside := PutResponse;
                awaitingReply := FALSE;
            }
        }
    }
    {
    sendDisconnectRequest:
        \* Disconnect is unconditional and its own critical section is pure (no network
        \* wait), so without a guard it reliably wins the race against Get/Put/
        \* ClockUpdate's own first send -- a client would disconnect before ever issuing a
        \* real request. This await is not part of the original algorithm; it only delays
        \* when disconnection becomes eligible, so client c's other threads get to run.
        await clock > MaxClock;
        clock := -1;
        multicast(replicasNetwork, [dst \in ReplicaSet |-> [op |-> DisconnectMessage, key |-> NoValue, value |-> NoValue, client |-> self, timestamp |-> 0, reply_to |-> self]]);
    }
    {
    clockUpdateLoop:
        while (clock # -1) {
            if (clock # -1) {
                clock := clock + 1;
                multicast(replicasNetwork, [dst \in ReplicaSet |-> [op |-> NullMessage, key |-> NoValue, value |-> NoValue, client |-> self, timestamp |-> clock, reply_to |-> self]]);
            }
        }
    }
}*)
\*BEGIN TRANSLATION
\*END TRANSLATION
(*
\* getRequest/putRequest/clockUpdateLoop keep ticking `clock` regardless of MaxClock --
\* only sendDisconnectRequest's guard (clock > MaxClock) cares, and nothing forces that
\* action to actually fire once enabled. So `clock` is genuinely unbounded in the reachable
\* state graph, not merely large; without this, TLC's BFS never terminates. The +1 slack
\* lets TLC still reach the state where sendDisconnectRequest's guard just became true
\* before it prunes further growth on that branch.
ClockBound == \A cl \in ClientSet: clock[cl] <= MaxClock + 1


\* TypeOK below is induced directly from the \@type annotations on the algorithm
\* above; it is TLC-only bookkeeping, not consumed by `fugue compile`.
\* Generic Address, needed only for nextClient: its initial value is a replica's
\* own `self` (see file header), every later value a client's -- the one variable
\* that isn't provably confined to just ReplicaSet or just ClientSet.
Address == ReplicaSet \cup ClientSet

\* Mirrors the two `Channel(...)` payload annotations on replicasNetwork/clientMailboxes.
RequestMessage ==
  [op:STRING,
    key:STRING,
    value:STRING,
    client:Address,
    timestamp:Int,
    reply_to:Address
  ]
ResponseMessage == [type:STRING, result:STRING ]

TypeOK ==
  /\ replicasNetwork \in [ReplicaSet -> Seq(RequestMessage)]
  /\ clientMailboxes \in [ClientSet -> Seq(ResponseMessage)]
  /\ liveClients \in [ReplicaSet -> SUBSET ClientSet]
  /\ pendingRequests \in [ReplicaSet -> [ClientSet -> Seq(RequestMessage)]]
  /\ stableMessages \in [ReplicaSet -> Seq(RequestMessage)]
  /\ i \in [ReplicaSet -> Int \cup { defaultInitValue }]
  /\ firstPending \in [ReplicaSet -> RequestMessage \cup { defaultInitValue }]
  /\ timestamp \in [ReplicaSet -> Int \cup { defaultInitValue }]
  /\ nextClient \in [ReplicaSet -> Address \cup { defaultInitValue }]
  /\ lowestPending \in [ReplicaSet -> Int \cup { defaultInitValue }]
  /\ chooseMessage \in [ReplicaSet -> BOOLEAN \cup { defaultInitValue }]
  /\ currentClocks \in [ReplicaSet -> [ClientSet -> Int]]
  /\ minClock \in [ReplicaSet -> Int \cup { defaultInitValue }]
  /\ continue \in [ReplicaSet -> BOOLEAN \cup { defaultInitValue }]
  /\ pendingClients \in
       [ReplicaSet -> ( SUBSET Address ) \cup { defaultInitValue }]
  /\ clientsIter \in
       [ReplicaSet -> ( SUBSET Address ) \cup { defaultInitValue }]
  /\ msg \in [ReplicaSet -> RequestMessage \cup { defaultInitValue }]
  /\ kv \in [ReplicaSet -> [KeySpace -> STRING]]
  /\ clock \in [ClientSet -> Int]
  /\ outside \in [ClientSet -> STRING]
  /\ awaitingReply \in [ClientSet -> BOOLEAN]
  /\ resp \in [ClientSet -> ResponseMessage \cup { defaultInitValue }]
  /\ putI \in [ClientSet -> Int \cup { defaultInitValue }]
*)
==============================================================================
