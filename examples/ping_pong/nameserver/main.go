// Command nameserver runs the rendezvous point the PingPongs example's Ping
// and Pong processes register with and resolve each other through; see
// ../ping, ../pong, and runtime/comm/tcp.ServeNameServer.
//
// Usage: nameserver <bind-addr>
package main

import (
	"log"
	"os"

	"github.com/mesabloo/fugue/runtime/comm/tcp"
)

func main() {
	if len(os.Args) != 2 {
		log.Fatalf("usage: %s <bind-addr>", os.Args[0])
	}
	bind := os.Args[1]

	log.Printf("name server listening on %s", bind)
	if err := tcp.ServeNameServer(bind); err != nil {
		log.Fatal(err)
	}
}
