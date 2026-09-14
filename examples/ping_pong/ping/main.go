// Command ping runs PingPongs.tla's Ping process as a standalone OS process,
// reachable by its Pong peers over TCP through the name-server-mediated
// wiring in runtime/comm/tcp; see ../README.md.
//
// Usage: ping <nameserver-addr> <pong-name>...
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
	if len(os.Args) < 3 {
		log.Fatalf("usage: %s <nameserver-addr> <pong-name>...", os.Args[0])
	}
	nameserver := os.Args[1]
	pongNames := os.Args[2:]

	self := tcp.Name("Ping")
	rawMailbox, addr, err := tcp.Listen[pingMsg]("127.0.0.1:0")
	if err != nil {
		log.Fatalf("listen: %v", err)
	}
	mailbox := debug.LogReceiver(self, rawMailbox)
	if err := tcp.Register(nameserver, string(self), addr); err != nil {
		log.Fatalf("register with name server at %s: %v", nameserver, err)
	}
	log.Printf("Ping: listening on %s, registered with name server at %s", addr, nameserver)

	pong := map[comm.Address]comm.Sender[tlaplus.Str]{}
	for _, name := range pongNames {
		peer, err := tcp.Lookup(nameserver, name)
		if err != nil {
			log.Fatalf("lookup %s: %v", name, err)
		}
		pong[tcp.Name(name)] = debug.LogSender(self, tcp.Name(name), tcp.Dial[tlaplus.Str](peer))
		log.Printf("Ping: resolved %s at %s", name, peer)
	}

	<-spec.Proc_Ping(spec.Net_Network{Pong: pong}, mailbox, self)
}
