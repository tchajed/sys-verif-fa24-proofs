package sharded_hashmap

import (
	"github.com/stretchr/testify/assert"
	"sync"
	"testing"
)

func TestStoreLoad(t *testing.T) {
	assert := assert.New(t)

	h := NewHashMap(10)
	_, ok := h.Load(1)
	assert.False(ok)

	h.Store(1, 10)
	v, ok := h.Load(1)
	assert.True(ok)
	assert.Equal(uint64(10), v)

	h.Store(3, 30)
	v, _ = h.Load(3)
	assert.Equal(uint64(30), v)
	v, _ = h.Load(1)
	assert.Equal(uint64(10), v)
}

func TestConcurrentLoadStore(t *testing.T) {
	h := NewHashMap(10)
	// Concurrent load and store, checking that we don't panic or deadlock (but
	// not checking the actual results)
	done := make(chan struct{})
	go func() {
		for i := 0; i < 100; i++ {
			h.Store(uint32(i), uint64(i))
		}
		done <- struct{}{}
	}()
	go func() {
		for i := 0; i < 100; i++ {
			h.Load(uint32(i))
		}
		done <- struct{}{}
	}()
	<-done
	<-done
}

func TestConcurrentLoadStoreOrder(t *testing.T) {
	h := NewHashMap(5)

	// Check that loads observe stores in the right order.

	wg := &sync.WaitGroup{}

	wg.Add(1)
	go func() {
		for i := 0; i < 100; i++ {
			h.Store(uint32(i), uint64(i*10))
		}
		wg.Done()
	}()

	// do 10 concurrent tests of load ordering
	for load_i := 0; load_i < 10; load_i++ {
		wg.Add(1)
		go func() {
			// once one load returns true, the rest should, too
			found := false
			for i := 100; i > 0; i-- {
				_, ok := h.Load(uint32(i))
				if found {
					assert.True(t, ok)
				}
				if ok {
					found = true
				}
			}
			wg.Done()
		}()
	}
	wg.Wait()
}
