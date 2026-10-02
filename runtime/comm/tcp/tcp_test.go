package tcp

import (
	"testing"
	"time"

	"github.com/mesabloo/fugue/runtime/comm"
	"github.com/mesabloo/fugue/runtime/comm/nameserver"
	"github.com/mesabloo/fugue/runtime/tlaplus"
)

// TestEndpointRoundTripCarriesAddress sends the shape Ping-Pong's ping channel
// carries — a record with a Str and an interface-typed address — through a
// Dial/Listen pair, checking both that gob moves it and that the address
// arrives as a nameserver.Name that compares equal to the one that was sent.
func TestEndpointRoundTripCarriesAddress(t *testing.T) {
	type message = struct {
		From comm.Address
		Mes  tlaplus.Str
	}

	mailbox, addr, err := Listen[message]("127.0.0.1:0")
	if err != nil {
		t.Fatalf("Listen: %v", err)
	}

	out := Dial[message](addr)
	out.Send(message{From: nameserver.Name("Pong1"), Mes: tlaplus.Str("Ping")})

	done := make(chan message, 1)
	go func() {
		v, _ := mailbox.Recv()
		done <- v
	}()

	select {
	case got := <-done:
		if got.Mes != "Ping" {
			t.Errorf("Mes = %q, want %q", got.Mes, "Ping")
		}
		if !comm.AddressOrd.Eq(got.From, comm.Address(nameserver.Name("Pong1"))) {
			t.Errorf("From = %v, want Name(Pong1)", got.From)
		}
	case <-time.After(time.Second):
		t.Fatal("nothing arrived at the mailbox")
	}
}
