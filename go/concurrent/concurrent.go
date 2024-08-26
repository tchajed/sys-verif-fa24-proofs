package concurrent

import (
	"sync"

	"github.com/goose-lang/std"
)

// will prove logical atomicity specs for AtomicInt

type AtomicInt struct {
	x  uint64
	mu *sync.Mutex
}

func NewAtomicInt() *AtomicInt {
	return &AtomicInt{x: 0, mu: new(sync.Mutex)}
}

func (i *AtomicInt) Get() uint64 {
	i.mu.Lock()
	x := i.x
	i.mu.Unlock()
	return x
}

func (i *AtomicInt) Inc(y uint64) {
	i.mu.Lock()
	i.x += y
	i.mu.Unlock()
}

func ParallelAdd1() uint64 {
	i := NewAtomicInt()
	h1 := std.Spawn(func() {
		i.Inc(2)
	})
	h2 := std.Spawn(func() {
		i.Inc(2)
	})
	h1.Join()
	h2.Join()
	return i.Get()
}

func ParallelAdd2() uint64 {
	var x uint64 = 0
	m := new(sync.Mutex)
	b := NewBarrier()
	b.Add(1)
	b.Add(1)
	go func() {
		m.Lock()
		x = std.SumAssumeNoOverflow(x, 2)
		m.Unlock()
		b.Done()
	}()
	go func() {
		m.Lock()
		x = std.SumAssumeNoOverflow(x, 2)
		m.Unlock()
		b.Done()
	}()

	b.Wait()
	m.Lock()
	x_now := x
	m.Unlock()
	return x_now
}
