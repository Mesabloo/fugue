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
EXTENDS Integers, Sequences, FiniteSets, Fugue

CONSTANTS
    \* @type: Set(Address);
    ReplicaSet,
    \* @type: Set(Address);
    ClientSet

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
KeySpace == {GetKey, PutKey}

\* @type: Str;
PutValue == "value1"
\* @type: Str;
NoValue == "none"

\* named so its type is fixed at the declaration rather than re-inferred where it's used --
\* an empty sequence literal used directly as a function-comprehension body doesn't pick up
\* the comprehension's expected codomain type.
\* @type: Seq({op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address});
EmptyRequestQueue == <<>>

(*--algorithm ReplicatedKVS {
    channels
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
            i,
            \* @type: {op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address};
            firstPending,
            \* @type: Int;
            timestamp,
            \* @type: Address;
            nextClient,
            \* @type: Int;
            lowestPending,
            \* @type: Bool;
            chooseMessage,
            \* last logical clock seen from each client
            \* @type: Address -> Int;
            currentClocks = [c \in ClientSet |-> 0],
            \* @type: Int;
            minClock,
            \* @type: Bool;
            continue,
            \* @type: Set(Address);
            pendingClients,
            \* @type: Set(Address);
            clientsIter,
            \* @type: {op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address};
            msg,
            \* @type: Str;
            ok,
            \* @type: Str;
            key,
            \* @type: Str;
            val,
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

        clientDisconnected:
            if (msg.op = DisconnectMessage) {
                liveClients := liveClients \ {msg.client};
            };

        replicaGetRequest:
            if (msg.op = GetMessage) {
                assert(msg.client \in liveClients);
                currentClocks[msg.client] := msg.timestamp;
                pendingRequests[msg.client] := Append(pendingRequests[msg.client], msg);
            };

        replicaPutRequest:
            if (msg.op = PutMessage) {
                currentClocks[msg.client] := msg.timestamp;
                pendingRequests[msg.client] := Append(pendingRequests[msg.client], msg);
            };

        replicaNullRequest:
            if (msg.op = NullMessage) {
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

            respondStableGet:
                if (msg.op = GetMessage) {
                    key := msg.key;
                    val := kv[key];
                    send(clientMailboxes[msg.reply_to], [type |-> GetResponse, result |-> val]);
                };

            respondStablePut:
                if (msg.op = PutMessage) {
                    key := msg.key;
                    val := msg.value;
                    kv[key] := val;
                    send(clientMailboxes[msg.reply_to], [type |-> PutResponse, result |-> ok]);
                };
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

            \* -- Get thread --
            \* @type: {op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address};
            getReq,
            \* @type: {type: Str, result: Str};
            getResp,

            \* -- Put thread --
            \* @type: Int;
            putI,
            \* @type: {op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address};
            putReq,
            \* @type: {type: Str, result: Str};
            putResp,

            \* -- Disconnect thread --
            \* @type: {op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address};
            discMsg,

            \* -- ClockUpdate thread --
            \* @type: {op: Str, key: Str, value: Str, client: Address, timestamp: Int, reply_to: Address};
            clockMsg;
    {
    getLoop:
        while (clock # -1) {
        getRequest:
            if (clock # -1) {
                clock := clock + 1;
                getReq := [op |-> GetMessage, key |-> GetKey, value |-> NoValue, client |-> self, timestamp |-> clock, reply_to |-> self];
                with (dst \in ReplicaSet) {
                    send(replicasNetwork[dst], getReq);
                };

            getReply:
                if (clock # -1) {
                    receive(clientMailboxes[self], getResp);
                    assert(getResp.type = GetResponse);
                    outside := getResp.result;
                }
            }
        }
    }
    {
    putLoop:
        while (clock # -1) {
        putRequest:
            if (clock # -1) {
                clock := clock + 1;
                putReq := [op |-> PutMessage, key |-> PutKey, value |-> PutValue, client |-> self, timestamp |-> clock, reply_to |-> self];
                putI := 0;

            putBroadcast:
                multicast(replicasNetwork, [dst \in ReplicaSet |-> putReq]);

            putResponse:
                while (putI < Cardinality(ReplicaSet)) {
                    if (clock = -1) {
                        goto putLoop;
                    } else {
                        receive(clientMailboxes[self], putResp);
                        assert(putResp.type = PutResponse);
                        putI := putI + 1;
                    }
                };

            putComplete:
                outside := PutResponse;
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
        await clock > 100;
        discMsg := [op |-> DisconnectMessage, key |-> NoValue, value |-> NoValue, client |-> self, timestamp |-> 0, reply_to |-> self];
        clock := -1;

    disconnectBroadcast:
        multicast(replicasNetwork, [dst \in ReplicaSet |-> discMsg]);
    }
    {
    clockUpdateLoop:
        while (clock # -1) {
            if (clock # -1) {
                clock := clock + 1;
                clockMsg := [op |-> NullMessage, key |-> NoValue, value |-> NoValue, client |-> self, timestamp |-> clock, reply_to |-> self];

            nullBroadcast:
                multicast(replicasNetwork, [dst \in ReplicaSet |-> clockMsg]);
            }
        }
    }
}*)

==============================================================================
