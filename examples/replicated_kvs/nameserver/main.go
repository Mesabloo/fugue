// Command nameserver runs the rendezvous point ReplicatedKVS.tla's replicas and clients
// register with and resolve each other through; see ../replica, ../client, and
// runtime/comm/tcp.ServeNameServer. It must be reachable before any replica or client
// registers, but they themselves may start in any order.
package main

import (
	"flag"
	"log"

	"github.com/mesabloo/fugue/runtime/comm/tcp"
)

func main() {
	bind := flag.String("bind", "127.0.0.1:9000", "address to listen on")
	flag.Parse()

	log.Printf("name server listening on %s", *bind)
	if err := tcp.ServeNameServer(*bind); err != nil {
		log.Fatal(err)
	}
}
