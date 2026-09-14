package condlocks

import (
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// guarded stands in for the struct of process-local variables a lock covers.
type guarded struct {
	counter int
	seen    []int
}

func TestMkLockHoldsInitialValue(t *testing.T) {
	l := MkLock(guarded{counter: 3})

	got := l.Acquire()
	if got.counter != 3 {
		t.Errorf("Acquire returned %d, want the initial 3", got.counter)
	}
	l.Release(got)
}

// TestAcquireReleaseRoundTrip checks that a released value is what the next
// acquirer sees — the mechanism by which a block's writes become visible.
func TestAcquireReleaseRoundTrip(t *testing.T) {
	l := MkLock(guarded{counter: 0})

	v := l.Acquire()
	v.counter = 7
	l.Release(v)

	if got := l.Acquire(); got.counter != 7 {
		t.Errorf("second Acquire returned %d, want the released 7", got.counter)
	}
}

// TestAcquireBlocksWhileHeld is the actual mutual-exclusion property at its
// smallest: a second acquisition must not succeed until the first releases.
func TestAcquireBlocksWhileHeld(t *testing.T) {
	l := MkLock(guarded{})
	held := l.Acquire()

	acquired := make(chan struct{})
	go func() {
		l.Release(l.Acquire())
		close(acquired)
	}()

	select {
	case <-acquired:
		t.Fatalf("Acquire succeeded while the lock was held")
	case <-time.After(50 * time.Millisecond):
	}

	l.Release(held)

	select {
	case <-acquired:
	case <-time.After(time.Second):
		t.Errorf("Acquire did not succeed after the lock was released")
	}
}

// TestMutualExclusion is the property lock inference exists to provide:
// concurrent read-modify-write cycles through the lock must not lose updates.
//
// Run this with -race to check the stronger claim, that the guarded value is
// never touched by two goroutines at once.
func TestMutualExclusion(t *testing.T) {
	const goroutines = 50
	const increments = 200

	l := MkLock(guarded{})

	var wg sync.WaitGroup
	for i := range goroutines {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for range increments {
				v := l.Acquire()
				counter := v.counter
				counter++
				l.Release(guarded{counter: counter, seen: append(v.seen, i)})
			}
		}()
	}
	wg.Wait()

	final := l.Acquire()
	if want := goroutines * increments; final.counter != want {
		t.Errorf("counter = %d, want %d: updates were lost", final.counter, want)
	}
	if len(final.seen) != goroutines*increments {
		t.Errorf("seen has %d entries, want %d", len(final.seen), goroutines*increments)
	}
}

// TestLocksAreOrderedByCaller documents the deadlock that lock inference's
// total order exists to prevent, by showing the safe case works: two locks
// acquired in the same order by both goroutines.
func TestLocksAreOrderedByCaller(t *testing.T) {
	first, second := MkLock(guarded{}), MkLock(guarded{})

	done := make(chan struct{})
	for range 2 {
		go func() {
			for range 100 {
				a := first.Acquire()
				b := second.Acquire()
				a.counter++
				b.counter++
				second.Release(b)
				first.Release(a)
			}
			done <- struct{}{}
		}()
	}

	for range 2 {
		select {
		case <-done:
		case <-time.After(5 * time.Second):
			t.Fatalf("deadlocked acquiring two locks in a consistent order")
		}
	}
}

// TestChangedFiresOnRelease is the whole point of this package over
// runtime/locks: a real mutation must wake anyone watching Changed().
func TestChangedFiresOnRelease(t *testing.T) {
	l := MkLock(guarded{})
	ch := l.Changed()

	select {
	case <-ch:
		t.Fatalf("Changed fired before any Release")
	default:
	}

	l.Release(l.Acquire())

	select {
	case <-ch:
	case <-time.After(time.Second):
		t.Errorf("Changed did not fire after Release")
	}
}

// TestChangedDoesNotFireOnReleaseNoBroadcast: the guard-false path must not
// wake anyone — nothing changed, and a spurious wake here would reintroduce
// exactly the wasted-cycle cost this design exists to avoid.
func TestChangedDoesNotFireOnReleaseNoBroadcast(t *testing.T) {
	l := MkLock(guarded{})
	v := l.Acquire()
	ch := l.ReleaseNoBroadcast(v)

	select {
	case <-ch:
		t.Fatalf("Changed fired after ReleaseNoBroadcast, which changed nothing")
	case <-time.After(50 * time.Millisecond):
	}

	// Confirm this channel isn't simply dead — it must still fire once a real
	// Release happens, so the silence above is meaningful.
	l.Release(l.Acquire())
	select {
	case <-ch:
	case <-time.After(time.Second):
		t.Errorf("Changed never fired even after a later real Release")
	}
}

// TestSnapshotSurvivesRaceWithConcurrentRelease is the correctness property
// the whole design hinges on: a Changed() snapshot taken before releasing
// must still fire even when the actual swap-and-close from a real,
// concurrent Release lands immediately after this goroutine's own release
// returns. Missing this would mean a permanently missed wakeup whenever a
// change and a guard-false retry race closely enough.
func TestSnapshotSurvivesRaceWithConcurrentRelease(t *testing.T) {
	const rounds = 2000
	l := MkLock(0)

	for i := 0; i < rounds; i++ {
		v := l.Acquire()
		ch := l.ReleaseNoBroadcast(v) // snapshot before release, guard was "false"

		done := make(chan struct{})
		go func() {
			l.Release(l.Acquire() + 1) // a real, concurrent change
			close(done)
		}()

		select {
		case <-ch:
		case <-time.After(time.Second):
			t.Fatalf("round %d: missed a wakeup for a change that raced right after release", i)
		}
		<-done
	}
}

// TestArbiterSharesStateAcrossCopies is Arbiter's whole reason to exist:
// generated code has no pointer type to keep a *sync.Once straight across
// goroutines, so Arbiter has to keep arbitrating correctly after being
// passed by value — copied into a slice, handed to N goroutines by value —
// the same way a Lock does.
func TestArbiterSharesStateAcrossCopies(t *testing.T) {
	a := MkArbiter()
	copies := make([]Arbiter, 10)
	for i := range copies {
		copies[i] = a // by value, as every generated function parameter is
	}

	var ran atomic.Int32
	var wg sync.WaitGroup
	for i := range copies {
		wg.Add(1)
		go func(a Arbiter) {
			defer wg.Done()
			a.Do(func() { ran.Add(1) })
		}(copies[i])
	}
	wg.Wait()

	if got := ran.Load(); got != 1 {
		t.Fatalf("Do ran %d times across copies of the same Arbiter, want exactly 1", got)
	}
}

// TestOnceArbitratesDisjointBranches models the shape compiled code actually
// uses: several goroutines race on a shared Arbiter and cancel channel, each
// independently finding its own guard true on a lock disjoint from every
// other's — lock exclusivity alone does nothing to serialize them. Exactly
// one must run its action; every other must release its lock unchanged,
// never having run anything.
func TestOnceArbitratesDisjointBranches(t *testing.T) {
	const branches = 20

	locks := make([]Lock[int], branches)
	for i := range locks {
		locks[i] = MkLock(i)
	}

	arbiter := MkArbiter()
	cancel := make(chan struct{})
	var ran atomic.Int32
	winner := make(chan int, 1)

	var wg sync.WaitGroup
	for i := range branches {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			v := locks[i].Acquire()
			// Guard true unconditionally: this branch's condition depends
			// only on its own lock, already satisfied.
			won := false
			arbiter.Do(func() {
				ran.Add(1)
				close(cancel)
				locks[i].Release(v + 1000)
				won = true
				winner <- i
			})
			if !won {
				locks[i].ReleaseNoBroadcast(v)
			}
		}(i)
	}
	wg.Wait()

	if got := ran.Load(); got != 1 {
		t.Fatalf("once body ran %d times, want exactly 1", got)
	}
	w := <-winner
	for i := range locks {
		got := locks[i].Acquire()
		if i == w {
			if got != i+1000 {
				t.Errorf("winner %d: lock holds %d, want %d", i, got, i+1000)
			}
		} else if got != i {
			t.Errorf("loser %d: lock holds %d, want unchanged %d (ran its action after losing)", i, got, i)
		}
	}
}
