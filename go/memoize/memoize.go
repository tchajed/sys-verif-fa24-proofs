package memoize

import "github.com/goose-lang/primitive"

// Memoize wraps a (slow) function and caches its results
type Memoize struct {
	f       func(uint64) uint64
	results map[uint64]uint64
}

func NewMemoize(f func(uint64) uint64) Memoize {
	return Memoize{
		f:       f,
		results: make(map[uint64]uint64),
	}
}

func (m Memoize) Call(x uint64) uint64 {
	cached, ok := m.results[x]
	if ok {
		return cached
	}
	y := m.f(x)
	m.results[x] = y
	return y
}

func UseMemoize1() {
	m := NewMemoize(func(x uint64) uint64 {
		return x * x
	})
	y1 := m.Call(3)
	primitive.Assert(y1 == 9)
	y2 := m.Call(3)
	primitive.Assert(y2 == 9)
	y3 := m.Call(5)
	primitive.Assert(y3 == 25)
}

func UseMemoize2(s []uint64) {
	sumUpto := func(n uint64) uint64 {
		if n > uint64(len(s)) {
			return 0
		}
		var sum uint64
		for i := uint64(0); i < n; i++ {
			sum += s[i]
		}
		return sum
	}

	m := NewMemoize(sumUpto)
	y1 := m.Call(3)
	y2 := m.Call(3)
	primitive.Assert(y1 == y2)
}

// MockMemoize has the same API as Memoize but with an implementation that
// doesn't actually save any results.
type MockMemoize struct {
	f func(uint64) uint64
}

func NewMockMemoize(f func(uint64) uint64) *MockMemoize {
	return &MockMemoize{f: f}
}

func (m *MockMemoize) Call(x uint64) uint64 {
	return m.f(x)
}
