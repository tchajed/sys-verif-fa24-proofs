package hashmap

import "sync"

type atomicPtr struct {
	mu  *sync.Mutex
	val map[uint64]uint64
}

func newAtomicPtr(m map[uint64]uint64) *atomicPtr {
	return &atomicPtr{mu: new(sync.Mutex), val: m}
}

func (a *atomicPtr) load() map[uint64]uint64 {
	a.mu.Lock()
	val := a.val
	a.mu.Unlock()
	return val
}

func (a *atomicPtr) store(m map[uint64]uint64) {
	a.mu.Lock()
	a.val = m
	a.mu.Unlock()
}

// A HashMap that supports concurrent reads by deep-cloning the map on every
// write.
//
// Modeled on DeepCopyMap in Go's [map_reference_test.go].
//
// (note that this is a reference implementation for testing the more
// sophisticated and actually used [sync.Map] implementation)
//
// [map_reference_test.go]: https://cs.opensource.google/go/go/+/refs/tags/go1.22.5:src/sync/map_reference_test.go
// [sync.Map]: https://pkg.go.dev/sync#Map
type HashMap struct {
	clean *atomicPtr
	mu    *sync.Mutex
}

func NewHashMap() *HashMap {
	var m = make(map[uint64]uint64)
	return &HashMap{clean: newAtomicPtr(m), mu: new(sync.Mutex)}
}

func (h *HashMap) Load(key uint64) (uint64, bool) {
	clean := h.clean.load()
	value, ok := clean[key]
	return value, ok
}

// Clone the input map by copying all values.
func mapClone(m map[uint64]uint64) map[uint64]uint64 {
	clone := make(map[uint64]uint64, len(m)+1)
	for k, v := range m {
		clone[k] = v
	}
	return clone
}

// Assuming mu is held, return an owned copy of the current clean map.
func (h *HashMap) dirty() map[uint64]uint64 {
	clean := h.clean.load()
	return mapClone(clean)
}

func (h *HashMap) Store(key uint64, value uint64) {
	h.mu.Lock()
	dirty := h.dirty()
	dirty[key] = value
	h.clean.store(dirty)
	h.mu.Unlock()
}

func (h *HashMap) Delete(key uint64) {
	h.mu.Lock()
	dirty := h.dirty()
	delete(dirty, key)
	h.clean.store(dirty)
	h.mu.Unlock()
}
