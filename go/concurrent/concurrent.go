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

func ParallelAdd3() uint64 {
	m := new(sync.Mutex)
	var i uint64 = 0
	h1 := std.Spawn(func() {
		m.Lock()
		i += 2
		m.Unlock()
	})
	h2 := std.Spawn(func() {
		m.Lock()
		i += 2
		m.Unlock()
	})
	h1.Join()
	h2.Join()
	m.Lock()
	y := i
	m.Unlock()
	return y
}

func ParallelAdd_Nthreads(n uint64) uint64 {
	m := new(sync.Mutex)
	var i uint64 = 0
	var handles []*std.JoinHandle
	for thread_i := uint64(0); thread_i < n; thread_i++ {
		h := std.Spawn(func() {
			m.Lock()
			i = std.SumAssumeNoOverflow(i, 2)
			m.Unlock()
		})
		handles = append(handles, h)
	}
	for _, h := range handles {
		h.Join()
	}
	m.Lock()
	y := i
	m.Unlock()
	return y
}
