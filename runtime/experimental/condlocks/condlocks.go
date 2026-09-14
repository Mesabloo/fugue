// Package condlocks provides the mutual exclusion and change notification the
// experimental -Xgo-cond compilation scheme uses to keep a compiled process's
// atomic blocks atomic without busy-waiting.
//
// Unlike runtime/locks, a Lock here also carries a "changed" signal: whoever
// actually mutates the guarded value (Release) closes the previous signal and
// installs a fresh one, waking anyone parked on Changed(). A release that
// leaves the value untouched (ReleaseNoBroadcast) does neither — nothing
// changed, nothing to announce, nothing woken.
package condlocks

import (
	"sync"
	"sync/atomic"
)

// Lock guards a group of process-local variables, carrying their values
// rather than sitting beside them, the same way runtime/locks.Lock does.
//
// cond is a pointer to the atomic pointer, not the atomic pointer itself:
// atomic.Pointer must never be copied after first use, and Lock is passed by
// value everywhere generated code passes a lock around — every branch,
// scheduler and thread function takes every lock as a plain parameter. The
// extra indirection is what keeps every copy of a Lock sharing the same
// change signal; val already has that property for free, being a channel.
type Lock[T any] struct {
	val  chan T
	cond *atomic.Pointer[chan struct{}]
}

// MkLock creates a lock already holding init, with a fresh, open change
// signal, so the guarded value is available to the first acquirer and the
// first waiter has something real to wait on.
func MkLock[T any](init T) Lock[T] {
	val := make(chan T, 1)
	val <- init
	var cond atomic.Pointer[chan struct{}]
	ch := make(chan struct{})
	cond.Store(&ch)
	return Lock[T]{val: val, cond: &cond}
}

// Acquire takes the guarded value, blocking until it is available.
//
// Never races against a cancellation signal: what it can block on is another
// holder's finite, straight-line critical section, not an unbounded external
// wait, so there is nothing worth interrupting it with.
func (l Lock[T]) Acquire() T {
	return <-l.val
}

// ReleaseNoBroadcast returns v as the new guarded value without announcing a
// change. For the guard-false path, where v is exactly what Acquire returned
// and nothing changed — waking anyone would be a pure spurious recheck.
//
// Returns the change signal to wait on next. Capturing it here, before v is
// handed back, is what makes the snapshot race-free: only a real Release can
// swap the signal, and nothing can Acquire — so nothing can Release — this
// lock until the send below completes.
func (l Lock[T]) ReleaseNoBroadcast(v T) chan struct{} {
	ch := l.Changed()
	l.val <- v
	return ch
}

// Release returns v as the new guarded value and wakes everyone waiting on
// Changed().
//
// The swap happens before the value is handed back, not after: swapping
// first keeps this call the only one touching cond until it is done, so a
// fast next-acquirer's own Release can never load the same old signal and
// double-close it.
func (l Lock[T]) Release(v T) {
	ch := make(chan struct{})
	old := l.cond.Swap(&ch)
	l.val <- v
	close(*old)
}

// Changed returns the channel that closes the next time this lock's value is
// actually mutated through Release (never ReleaseNoBroadcast). Capture it
// before releasing — see ReleaseNoBroadcast and Release — or the snapshot can
// silently target an already-superseded signal.
func (l Lock[T]) Changed() chan struct{} {
	return *l.cond.Load()
}

// Arbiter picks exactly one winner among however many callers race Do — the
// same guarantee sync.Once gives a single shared *Once, wrapped so it stays
// safe to pass by value. Generated code has no address-of operator or
// pointer type to keep a *sync.Once straight across the goroutines one
// atomic block's branches run as; Arbiter hides that indirection the same
// way Lock hides cond's.
type Arbiter struct {
	once *sync.Once
}

// MkArbiter creates a fresh arbiter, good for exactly one block instance —
// like cancel, a new one is made every time the block containing it starts.
func MkArbiter() Arbiter {
	return Arbiter{once: new(sync.Once)}
}

// Do runs f if no other call on this Arbiter has, blocking until whichever
// call wins (there or already in progress elsewhere) has returned. Every
// other caller's f is never invoked, matching sync.Once.Do exactly.
func (a Arbiter) Do(f func()) {
	a.once.Do(f)
}
