// Command nameserver runs the rendezvous point the Paxos example's nodes
// register with and resolve each other through; see ../main.go and
// runtime/comm/nameserver.Serve. It must be reachable before any node
// registers, but nodes themselves may start in any order.
package main

import (
	"flag"
	"log"

	"github.com/mesabloo/fugue/runtime/comm/nameserver"
)

func main() {
	bind := flag.String("bind", "127.0.0.1:9000", "address to listen on")
	flag.Parse()

	log.Printf("name server listening on %s", *bind)
	if err := nameserver.Serve(*bind); err != nil {
		log.Fatal(err)
	}
}
