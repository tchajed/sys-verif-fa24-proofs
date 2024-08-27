package heap_test

import (
	"sys_verif_code/heap"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestStackBasic(t *testing.T) {
	assert := assert.New(t)
	s := heap.NewStack()

	s.Push(1)
	s.Push(2)
	x, ok := s.Pop()
	assert.True(ok)
	assert.Equal(x, uint64(2))
}

func TestQueue(t *testing.T) {
	assert := assert.New(t)
	q := heap.NewQueue()

	x, ok := q.Pop()
	assert.False(ok)

	q.Push(1)
	q.Push(2)
	q.Push(3)

	x, ok = q.Pop()
	assert.True(ok)
	assert.Equal(x, uint64(1))

	q.Pop() // 2
	q.Push(4)
	x, ok = q.Pop()
	assert.Equal(x, uint64(3))

	x, ok = q.Pop()
	assert.Equal(x, uint64(4))
}
