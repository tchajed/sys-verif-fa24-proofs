package concurrent

import (
	"sync"

	"github.com/goose-lang/std"
)

// See the master's thesis [Verifying a Barrier using Iris] for ideas on how to
// specify a barrier using ownership in Iris.
//
// [Verifying a Barrier using Iris]:
// https://www.cs.ru.nl/bachelors-theses/2023/Simcha_van_Collem___1040283___Verifying_a_Barrier_using_Iris.pdf

// A simple barrier, very similar to a Go `sync.WaitGroup`. We prove a spec that
// allows only one thread to call `Wait()`, but subsequent calls will return
// immediately and the implementation should satisfy a more general
// specification.
type Barrier struct {
	numWaiting uint64
	mu         *sync.Mutex
	cond       *sync.Cond
}

// Create a new barrier waiting for no threads.
func NewBarrier() *Barrier {
	mu := new(sync.Mutex)
	cond := sync.NewCond(mu)
	return &Barrier{numWaiting: 0, mu: mu, cond: cond}
}

// Add `n` threads that the barrier is waiting to call `Done()`.
func (b *Barrier) Add(n uint64) {
	b.mu.Lock()
	b.numWaiting = std.SumAssumeNoOverflow(b.numWaiting, n)
	b.mu.Unlock()
}

// Mark one thread as done.
func (b *Barrier) Done() {
	b.mu.Lock()
	if b.numWaiting == 0 {
		panic("Done() called too many times")
	}
	b.numWaiting = b.numWaiting - 1
	if b.numWaiting == 0 {
		b.cond.Broadcast()
	}
	b.mu.Unlock()
}

// Wait blocks until all threads pending with `Add()` have called `Done()`.
func (b *Barrier) Wait() {
	b.mu.Lock()
	for b.numWaiting > 0 {
		b.cond.Wait()
	}
	b.mu.Unlock()
}
