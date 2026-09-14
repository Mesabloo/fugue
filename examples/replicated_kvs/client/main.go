// Command client runs one client of ReplicatedKVS.tla as a standalone OS process, running
// all four of the client's threads (Get-loop, Put-loop, Disconnect, ClockUpdate-loop, see
// ReplicatedKVS.tla's file header) concurrently and reachable by replicas over TCP through
// the name-server-mediated wiring in runtime/comm/tcp; see ../README.md. -name picks which
// of spec.ClientNames this process is.
//
// Usage: client -name <c1|c2> [-bind addr] [-ns addr]
package main

import (
	"flag"
	"log"

	"github.com/mesabloo/fugue/examples/replicated_kvs/spec"
	"github.com/mesabloo/fugue/runtime/comm"
	"github.com/mesabloo/fugue/runtime/comm/tcp"
	"github.com/mesabloo/fugue/runtime/debug"
	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// requestMsg mirrors replicasNetwork's mailbox message record, field for field, in the same
// order (Go struct identity is order-sensitive).
type requestMsg = struct {
	Client    comm.Address
	Key       tlaplus.Str
	Op        tlaplus.Str
	Reply__to comm.Address
	Timestamp tlaplus.Int
	Value     tlaplus.Str
}

// responseMsg mirrors this client's own mailbox message record, field for field.
type responseMsg = struct {
	Result tlaplus.Str
	Type   tlaplus.Str
}

func main() {
	name := flag.String("name", "", "this client's name (one of c1, c2)")
	bind := flag.String("bind", "127.0.0.1:0", "address to listen on for this client's mailbox")
	ns := flag.String("ns", "127.0.0.1:9000", "name server address")
	flag.Parse()

	if !spec.ValidClientName(*name) {
		log.Fatalf("-name must be one of %v, got %q", spec.ClientNames, *name)
	}
	self := tcp.Name(*name)

	rawMailbox, addr, err := tcp.Listen[responseMsg](*bind)
	if err != nil {
		log.Fatalf("listen on %s: %v", *bind, err)
	}
	mailbox := debug.LogReceiver(self, rawMailbox)
	if err := tcp.Register(*ns, *name, addr); err != nil {
		log.Fatalf("register %s with name server at %s: %v", *name, *ns, err)
	}
	log.Printf("%s: listening on %s, registered with name server at %s", *name, addr, *ns)

	// A client only ever sends to replicas (Get picks one, Put/Disconnect/ClockUpdate
	// multicast to all), so it needs every replica's mailbox resolved up front -- it never
	// sends to another client, so ClientMailboxes is left nil.
	replicasNetwork := map[comm.Address]comm.Sender[requestMsg]{}
	for _, r := range spec.ReplicaNames {
		peer, err := tcp.Lookup(*ns, r)
		if err != nil {
			log.Fatalf("lookup replica %s: %v", r, err)
		}
		replicasNetwork[tcp.Name(r)] = debug.LogSender(self, tcp.Name(r), tcp.Dial[requestMsg](peer))
		log.Printf("%s: resolved replica %s at %s", *name, r, peer)
	}

	net := spec.Net_Network{ReplicasNetwork: replicasNetwork}
	<-spec.Proc_c(net, mailbox, self) // getLoop/putLoop/clockUpdateLoop run forever; this blocks forever too.
}
