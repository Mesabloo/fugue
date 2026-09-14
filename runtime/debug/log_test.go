package debug

import (
	"testing"

	"github.com/mesabloo/fugue/runtime/comm"
)

// goChan is a Sender/Receiver backed by a Go channel, the same minimal stand-in
// runtime/comm's own tests use to pin the endpoint contract without a real transport.
type goChan[T any] chan T

func (c goChan[T]) Send(value T) { c <- value }

func (c goChan[T]) Recv() (T, bool) {
	v, ok := <-c
	return v, ok
}

// testAddress is a minimal comm.Address, the same stand-in runtime/comm's own tests use --
// LogSender/LogReceiver only ever pass an Address through to log.Printf's %v, so nothing
// about its Eq/Lt is exercised here.
type testAddress int

func (a testAddress) Eq(other comm.Address) bool { return a == other.(testAddress) }
func (a testAddress) Lt(other comm.Address) bool { return a < other.(testAddress) }

// TestLogSenderDelegates pins that wrapping a Sender changes nothing about what it
// delivers -- the decorator's only job is to log on the way through.
func TestLogSenderDelegates(t *testing.T) {
	c := make(goChan[int], 1)
	s := LogSender(testAddress(1), testAddress(2), c)

	s.Send(42)
	if got := <-c; got != 42 {
		t.Errorf("delegated Send delivered %d, want 42", got)
	}
}

// TestLogReceiverDelegates is the receiving half: the value and the "medium alive" flag
// both pass through unchanged.
func TestLogReceiverDelegates(t *testing.T) {
	c := make(goChan[int], 1)
	c.Send(7)
	r := LogReceiver(testAddress(1), c)

	got, ok := r.Recv()
	if !ok || got != 7 {
		t.Errorf("delegated Recv = (%d, %v), want (7, true)", got, ok)
	}
}

// TestLogReceiverDelegatesVanishedMedium: a closed channel's "gone" report must reach the
// caller through the wrapper too, unlogged since there is no value to show.
func TestLogReceiverDelegatesVanishedMedium(t *testing.T) {
	c := make(goChan[int])
	close(c)
	r := LogReceiver(testAddress(1), c)

	if got, ok := r.Recv(); ok || got != 0 {
		t.Errorf("delegated Recv on a closed medium = (%d, %v), want (0, false)", got, ok)
	}
}
