// Command replica runs one replica of ReplicatedKVS.tla as a standalone OS process,
// reachable by its clients over TCP through the name-server-mediated wiring in
// runtime/comm/tcp; see ../README.md. -name picks which of
// replicatedkvs.ReplicaNames this process is.
//
// Usage: replica -name <r1|r2|r3> [-bind addr] [-ns addr]
package main

import (
	"flag"
	"log"

	"github.com/mesabloo/fugue/examples/replicated_kvs/replicatedkvs"
	"github.com/mesabloo/fugue/runtime/comm"
	"github.com/mesabloo/fugue/runtime/comm/tcp"
	"github.com/mesabloo/fugue/runtime/debug"
	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// requestMsg mirrors replicasNetwork's mailbox message record field for field, in the same
// order (Go struct identity is order-sensitive) -- Go structs are structurally typed, so a
// local alias is enough, matching examples/paxos/main.go's Msg/Ballot aliases.
type requestMsg = struct {
	Client    comm.Address
	Key       tlaplus.Str
	Op        tlaplus.Str
	Reply__to comm.Address
	Timestamp tlaplus.Int
	Value     tlaplus.Str
}

// responseMsg mirrors clientMailboxes' mailbox message record, field for field.
type responseMsg = struct {
	Result tlaplus.Str
	Type   tlaplus.Str
}

func main() {
	name := flag.String("name", "", "this replica's name (one of r1, r2, r3)")
	bind := flag.String("bind", "127.0.0.1:0", "address to listen on for this replica's mailbox")
	ns := flag.String("ns", "127.0.0.1:9000", "name server address")
	flag.Parse()

	if !replicatedkvs.ValidReplicaName(*name) {
		log.Fatalf("-name must be one of %v, got %q", replicatedkvs.ReplicaNames, *name)
	}
	self := tcp.Name(*name)

	rawMailbox, addr, err := tcp.Listen[requestMsg](*bind)
	if err != nil {
		log.Fatalf("listen on %s: %v", *bind, err)
	}
	mailbox := debug.LogReceiver(self, rawMailbox)
	if err := tcp.Register(*ns, *name, addr); err != nil {
		log.Fatalf("register %s with name server at %s: %v", *name, *ns, err)
	}
	log.Printf("%s: listening on %s, registered with name server at %s", *name, addr, *ns)

	// A replica only ever replies to whichever client sent it a request, so it needs every
	// client's mailbox resolved up front -- it never sends to another replica, so
	// ReplicasNetwork is left nil.
	clientMailboxes := map[comm.Address]comm.Sender[responseMsg]{}
	for _, c := range replicatedkvs.ClientNames {
		peer, err := tcp.Lookup(*ns, c)
		if err != nil {
			log.Fatalf("lookup client %s: %v", c, err)
		}
		clientMailboxes[tcp.Name(c)] = debug.LogSender(self, tcp.Name(c), tcp.Dial[responseMsg](peer))
		log.Printf("%s: resolved client %s at %s", *name, c, peer)
	}

	net := replicatedkvs.Net_Network{ClientMailboxes: clientMailboxes}
	<-replicatedkvs.Proc_r(net, mailbox, self) // replicaLoop runs forever; this blocks forever too.
}
