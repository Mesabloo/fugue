// Command pong runs one instance of PingPongs.tla's Pong process as a
// standalone OS process, reachable by Ping over TCP through the
// name-server-mediated wiring in runtime/comm/tcp; see ../README.md. Run it
// more than once, each time with a different <own-name>, for more than one Pong.
//
// Usage: pong <nameserver-addr> <own-name>
package main

import (
	"log"
	"os"

	"github.com/mesabloo/fugue/examples/ping_pong/spec"
	"github.com/mesabloo/fugue/runtime/comm"
	"github.com/mesabloo/fugue/runtime/comm/tcp"
	"github.com/mesabloo/fugue/runtime/debug"
	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// pingMsg mirrors the ping mailbox's message record field for field
// (Go structs are structurally typed, so a local alias is enough).
type pingMsg = struct {
	From comm.Address
	Mes  tlaplus.Str
}

func main() {
	if len(os.Args) != 3 {
		log.Fatalf("usage: %s <nameserver-addr> <own-name>", os.Args[0])
	}
	nameserver := os.Args[1]
	name := os.Args[2]
	self := tcp.Name(name)

	rawMailbox, addr, err := tcp.Listen[tlaplus.Str]("127.0.0.1:0")
	if err != nil {
		log.Fatalf("listen: %v", err)
	}
	mailbox := debug.LogReceiver(self, rawMailbox)
	if err := tcp.Register(nameserver, name, addr); err != nil {
		log.Fatalf("register with name server at %s: %v", nameserver, err)
	}
	log.Printf("%s: listening on %s, registered with name server at %s", name, addr, nameserver)

	peer, err := tcp.Lookup(nameserver, "Ping")
	if err != nil {
		log.Fatalf("lookup Ping: %v", err)
	}
	log.Printf("%s: resolved Ping at %s", name, peer)

	net := spec.Net_Network{Ping: debug.LogSender(self, tcp.Name("Ping"), tcp.Dial[pingMsg](peer))}
	<-spec.Proc_Pong(net, mailbox, self)
}
