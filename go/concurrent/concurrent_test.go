package concurrent

import (
	"fmt"
	"sync"
	"sync/atomic"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestAtomicInt_Get(t *testing.T) {
	assert := assert.New(t)

	// Create a new AtomicInt
	i := NewAtomicInt()

	// Set the initial value
	i.Inc(42)

	// Get the value and assert it is correct
	result := i.Get()
	assert.Equal(uint64(42), result, "Get")

	// Increment the value
	i.Inc(10)

	// Get the updated value and assert it is correct
	result = i.Get()
	assert.Equal(uint64(52), result, "Get")
}

func TestAtomicInt_concurrent(t *testing.T) {
	assert := assert.New(t)

	i := NewAtomicInt()

	// Set an initial value
	i.Inc(42)

	var wg sync.WaitGroup
	wg.Add(100)
	// Increment the value concurrently
	for j := 0; j < 100; j++ {
		go func() {
			i.Inc(1)
			wg.Done()
		}()
	}
	wg.Wait()

	// Get the updated value and assert it is correct
	result := i.Get()
	assert.Equal(uint64(142), result, "Get")
}

func TestParallelAdd2(t *testing.T) {
	assert := assert.New(t)

	for i := 0; i < 10; i++ {
		result := ParallelAdd2()
		assert.Equal(uint64(4), result, "ParallelAdd2")
	}
}

func TestBarrierN(t *testing.T) {
	numRun := atomic.Int64{}
	b := NewBarrier()
	b.Add(1)
	b.Add(2)
	for i := 0; i < 3; i++ {
		go func() {
			numRun.Add(1)
			b.Done()
		}()
	}
	b.Wait()
	assert.Equal(t, numRun.Load(), int64(3))
}

func TestBarrierNoAdd(t *testing.T) {
	b := NewBarrier()
	b.Wait()
}

func UseBarrierPrint() {
	b := NewBarrier()
	for i := 0; i < 3; i++ {
		b.Add(1)
		go func() {
			fmt.Printf("hello %d\n", i)
			b.Done()
		}()
	}
	b.Wait()

}
