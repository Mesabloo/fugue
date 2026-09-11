------------------------------- MODULE Paxos ---------------------------------
(****************************************************************************)
(* This is a representation of the core of the Paxos consensus algorithm in *)
(* Distributed PlusCal. Every node may play the role of leader, acceptor,   *)
(* and learner. Leader election is not modeled: any process that suspects   *)
(* the current leader to have crashed may initiate a new ballot.            *)
(****************************************************************************)
EXTENDS Integers, Bags, FiniteSets, Fugue

CONSTANTS
    \* number of nodes
    \* @type: Int;
    N,
    \* set of values that may be proposed / chosen
    \* @type: Set(Str);
    Values,      
    \* @type: Set(Address);
    Nodes,
    \* upper bound on ballot round numbers, so Ballots is finite and can compile to Go
    \* @type: Int;
    MaxRound

ASSUME IsFiniteSet(Nodes)
ASSUME Cardinality(Nodes) = N
ASSUME MaxRound > 0

\* Nodes == 1 .. N
\* @type: Int;
quorum == N \div 2

\* @type: Str;
None == "" \* CHOOSE none : none \notin Values


(****************************************************************************)
(* Ballots are pairs of natural numbers and node IDs where the latter       *)
(* indicates the node at the origin of the ballot. Therefore, ballots       *)
(* initiated by different nodes can be differentiated. Ballot IDs are       *)
(* ordered lexicographically.                                               *)
(****************************************************************************)
\* Bounded so ballot rounds are finite (needed to compile to Go at all -- MaxRound
\* below). Not referenced by the algorithm, which quantifies over 0..MaxRound-1 and
\* Nodes directly wherever it needs a ballot's round/node parts (see "learn a value"
\* below); kept here as the type this file's comments and any future TLC-only
\* invariant should describe a ballot by.
\* @type: Set(<<Int, Address>>);
Ballots == (0..MaxRound-1) \X Nodes

\* @type: (<<Int, Address>>, <<Int, Address>>) => Bool;
less(b1, b2) ==
   \/ b1[1] < b2[1]
   \/ b1[1] = b2[1] /\ b1[2] \prec b2[2]

(* PlusCal options (-distpcal) *)
(*--algorithm Paxos {
    fifos
        \* @type: Address -> Channel({type: Str, leader: Address, bal: <<Int, Address>>, val: Str, maxVBal: <<Int, Address>>, maxVal: Str});
        ch[Nodes];

    \* @mailbox: ch[self];
    process (node \in Nodes)
        variables
            \* the highest-number ballot the node has participated in
            maxBal = <<0,self>>,
            \* the highest-number ballot in which the node has voted
            maxVBal = <<0,self>>,
            \* the value the node voted for in that ballot
            maxVal = None,
            \* last message received (None unless handling a message)
            \* @type: {type: Str, leader: Address, bal: <<Int, Address>>, val: Str, maxVBal: <<Int, Address>>, maxVal: Str};
            msg = [type |-> "", leader |-> self, bal |-> <<0, self>>, val |-> "", maxVBal |-> <<0,self>>, maxVal |-> ""],
            \* ballot number used in latest "1a" message
            ballot1a = <<0,self>>,
            \* number of replies received by a leader to its "1a" message
            replies1a = 0,
            \* the highest maxVBal value the leader heard of
            maxVBalRcvd = <<0,self>>,
            \* the corresponding value
            maxValRcvd = None,
            \* bag of votes received by the node
            \* @type: Bag({bal: <<Int, Address>>, val: Str});
            votesRcvd = EmptyBag,
            \* value chosen by the node
            chosen = None;
    {  \* main thread of node
n0: 
        while (TRUE) {
            either {
                \* suspect the current leader to have crashed, start new ballot
                with (newBallot = << maxBal[1]+1, self >>) {
                    multicast(ch, [n \in Nodes \ {self} |->
                                    [type |-> "1a", leader |-> self,
                                    bal |-> newBallot, val |-> None,
                                    maxVBal |-> <<0,self>>, maxVal |-> None] ] );
                    maxBal := newBallot;
                    ballot1a := newBallot;
                    replies1a := 1; \* leader implicitly replies to its own message
                    maxVBalRcvd := maxVBal;
                    maxValRcvd := maxVal;
                }
            } or {
                \* received messages from a quorum of nodes in reply to "1a" message
                when (replies1a > quorum);
                \* if some reply contained a value, take the one in the reply for
                \* the highest ballot, otherwise choose any value
                \* (`with x \in S` is a search over S and Fugue only compiles a search
                \* into a deterministic pick, not a nondeterministic one, so this is
                \* written as a plain `=` binding to a CHOOSE instead)
                with (v = IF maxValRcvd # None THEN maxValRcvd ELSE CHOOSE x \in Values : TRUE) {
                    multicast(ch, [n \in Nodes \ {self} |->
                                    [type |-> "2a", leader |-> self,
                                    bal |-> ballot1a, val |-> v,
                                    maxVBal |-> <<0,self>>, maxVal |-> None]]);
                };
                \* stop handling "1b" messages and reset corresponding variables
                replies1a := 0;
                ballot1a := <<0,self>>;
                maxVBalRcvd := <<0,self>>;
                maxValRcvd := None;
            } or {
                \* learn a value when a quorum of nodes voted for it
                \* (Consistency guarantees at most one such value ever exists, so the
                \* CHOOSE below is exact, not an approximation)
                when (\E v \in Values : \E m \in BagToSet(votesRcvd) :
                                m.val = v /\ CopiesIn(m, votesRcvd) > quorum);
                with (v = CHOOSE v \in Values : \E m \in BagToSet(votesRcvd) :
                                m.val = v /\ CopiesIn(m, votesRcvd) > quorum) {
                    chosen := v;
                }
            }
        }
    }  \* end main thread
    {  \* helper thread for receiving messages
r0:  
        while (TRUE) {
            receive(ch[self], msg);
            if (msg.type = "1a" /\ less(maxBal, msg.bal)) {
                \* node participates in new ballot
                maxBal := msg.bal;
r0_1:           send(ch[msg.leader],
                            [type |-> "1b", leader |-> self,
                            bal |-> msg.bal, val |-> None,
                            maxVBal |-> maxVBal, maxVal |-> maxVal]);
                msg := [type |-> "", leader |-> self, bal |-> <<0,self>>, val |-> "", maxVBal |-> <<0,self>>, maxVal |-> ""];  \* reset to default value (reduce state space)
            } else if (msg.type = "1b" /\ msg.bal = ballot1a /\ replies1a > 0) {
                \* leader receives a reply to its previous "1a" message
                \* NB: replies1a = 0 means that the leader is no longer interested in "1b"
                \* messages because it has already sent a "2a" message.
                replies1a := replies1a + 1;
                \* record highest maxVBal value (if any) and corresponding value
                if (msg.maxVBal[1] # 0 /\ less(maxVBalRcvd, msg.maxVBal)) {
                    maxVBalRcvd := msg.maxVBal; maxValRcvd := msg.maxVal;
                };
r0_2:           msg := [type |-> "", leader |-> self, bal |-> <<0,self>>, val |-> "", maxVBal |-> <<0,self>>, maxVal |-> ""];
            } else if (msg.type = "2a" /\ (less(maxBal, msg.bal) \/ maxBal = msg.bal) /\ maxVBal # msg.bal) {
                maxBal := msg.bal;
                maxVBal := msg.bal;
                maxVal := msg.val;
                \* vote for value contained in "2a" message
r0_3:           multicast(ch, [n \in Nodes \ {self} |->
                                    [type |-> "2b", leader |-> self,
                                    bal |-> msg.bal, val |-> msg.val,
                                    maxVBal |-> <<0,self>>, maxVal |-> None]]);
                \* record the node's vote
                votesRcvd := votesRcvd (+)
                                SetToBag({[bal |-> msg.bal, val |-> msg.val]});
                msg := [type |-> "", leader |-> self, bal |-> <<0,self>>, val |-> "", maxVBal |-> <<0,self>>, maxVal |-> ""];
            } else if (msg.type = "2b") {
                \* record vote
                votesRcvd := votesRcvd (+)
                                SetToBag({[bal |-> msg.bal, val |-> msg.val]});
r0_4:           msg := [type |-> "", leader |-> self, bal |-> <<0,self>>, val |-> "", maxVBal |-> <<0,self>>, maxVal |-> ""];
            } else {
r0_5:           msg := [type |-> "", leader |-> self, bal |-> <<0,self>>, val |-> "", maxVBal |-> <<0,self>>, maxVal |-> ""];
            }
        }  \* end helper thread
    }
}*)

\* BEGIN TRANSLATION (chksum(pcal) = "75c82728" /\ chksum(tla) = "cc812100")


\* END TRANSLATION

(****************************************************************************)
(* Fugue has no shared module-level VARIABLE across processes (Core/       *)
(* GuardedPlusCal/Semantics/Process.lean bans a process from referencing    *)
(* any module-level VARIABLE) and never materializes the pcal-style         *)
(* `VARIABLES ch, maxBal, ...` a real translation would generate, so `ch`,  *)
(* `maxBal`, etc. below are not in scope for `fugue compile` -- these       *)
(* TLC-only invariants are kept as documentation and are not checked/      *)
(* compiled by Fugue.                                                      *)
(*
Messages ==
    [type: {"1a"}, leader: Nodes, bal: Ballots]
    \union
    [type: {"1b"}, bal: Ballots, maxVBal: Ballots, maxVal: Values \union {None}]
    \union
    [type: {"2a"}, leader: Nodes, bal: Ballots, val: Values]
    \union
    [type: {"2b"}, bal: Ballots, val: Values]

TypeOK ==
    /\ \A n \in Nodes : IsABag(ch[n])
    /\ \A n \in Nodes : \A m \in DOMAIN ch[n] : m \in Messages
    /\ maxBal \in [Nodes -> Ballots]
    /\ maxVBal \in [Nodes -> Ballots]
    /\ maxVal \in [Nodes -> Values \union {None}]
    /\ ballot1a \in [Nodes -> Ballots]
    /\ replies1a \in [Nodes -> Nat]
    /\ maxVBalRcvd \in [Nodes -> Ballots]
    /\ maxValRcvd \in [Nodes -> Values \union {None}]
    /\ \A n \in Nodes : IsABag(votesRcvd[n])
    /\ \A n \in Nodes : \A v \in BagToSet(votesRcvd[n]) : v \in [bal : Ballots, val : Values]
    /\ chosen \in [Nodes -> Values \union {None}]

(* Any two nodes that have chosen some value must agree. *)
Consistency ==
    /\ \A m,n \in Nodes : chosen[m] # None /\ chosen[n] # None
                          => chosen[m] = chosen[n]
*)
===============================================================================
