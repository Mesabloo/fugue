package nameserver

import (
	"net"
	"testing"
	"time"
)

// startNameServer brings up a name server on a free port and returns its
// address.
func startNameServer(t *testing.T) string {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("could not bind a name server listener: %v", err)
	}
	go serveOn(ln)
	return ln.Addr().String()
}

// TestLookupResolvesRegistration is the ordinary path: a name registered before
// it is looked up resolves to the address it was registered with.
func TestLookupResolvesRegistration(t *testing.T) {
	ns := startNameServer(t)

	if err := Register(ns, "Ping", "10.0.0.1:7001"); err != nil {
		t.Fatalf("Register: %v", err)
	}
	got, err := Lookup(ns, "Ping")
	if err != nil {
		t.Fatalf("Lookup: %v", err)
	}
	if got != "10.0.0.1:7001" {
		t.Errorf("Lookup(Ping) = %q, want %q", got, "10.0.0.1:7001")
	}
}

// TestLookupParksUntilRegistered pins the ordering guarantee: a Lookup for a
// name nobody has registered yet blocks rather than failing, and returns once
// the name arrives.
func TestLookupParksUntilRegistered(t *testing.T) {
	ns := startNameServer(t)

	resolved := make(chan string, 1)
	go func() {
		addr, err := Lookup(ns, "Pong1")
		if err != nil {
			t.Errorf("Lookup: %v", err)
		}
		resolved <- addr
	}()

	select {
	case <-resolved:
		t.Fatal("Lookup returned before the name was registered")
	case <-time.After(50 * time.Millisecond):
	}

	if err := Register(ns, "Pong1", "10.0.0.2:7002"); err != nil {
		t.Fatalf("Register: %v", err)
	}

	select {
	case addr := <-resolved:
		if addr != "10.0.0.2:7002" {
			t.Errorf("Lookup(Pong1) = %q, want %q", addr, "10.0.0.2:7002")
		}
	case <-time.After(time.Second):
		t.Fatal("Lookup did not return after the name was registered")
	}
}
