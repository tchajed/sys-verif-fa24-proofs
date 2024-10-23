package memoize

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
