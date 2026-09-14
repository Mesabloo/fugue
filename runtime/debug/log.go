// Package debug wraps runtime/comm's Sender/Receiver endpoints to log the values crossing
// them, for a compiled process whose specification has no `print` of its own -- the compiler
// emits no observability, and a running system built out of generated code is otherwise silent
// between its start and whatever it was meant to demonstrate.
//
// Nothing here is part of what fugue compile emits or requires; it is glue for whoever wires a
// runnable system together (a main, as examples/ping_pong and examples/paxos are), applied at
// that same site, around the same Sender/Receiver values the wiring already constructs.
package debug

import (
	"log"

	"github.com/mesabloo/fugue/runtime/comm"
)

// LogSender wraps s so every value sent through it is logged as "self -> to: value" before
// being handed to the real Sender.
func LogSender[T any](self, to comm.Address, s comm.Sender[T]) comm.Sender[T] {
	return loggingSender[T]{self: self, to: to, Sender: s}
}

type loggingSender[T any] struct {
	self, to comm.Address
	comm.Sender[T]
}

func (s loggingSender[T]) Send(value T) {
	log.Printf("%v -> %v: %+v", s.self, s.to, value)
	s.Sender.Send(value)
}

// LogReceiver wraps r so every value received through it is logged as "self <- value" once
// read from the real Receiver.
func LogReceiver[T any](self comm.Address, r comm.Receiver[T]) comm.Receiver[T] {
	return loggingReceiver[T]{self: self, Receiver: r}
}

type loggingReceiver[T any] struct {
	self comm.Address
	comm.Receiver[T]
}

func (r loggingReceiver[T]) Recv() (T, bool) {
	value, ok := r.Receiver.Recv()
	if ok {
		log.Printf("%v <- %+v", r.self, value)
	}
	return value, ok
}
