package heap_test

import (
	"sys_verif_code/heap"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestLinkedListInsertOnly(t *testing.T) {
	assert := assert.New(t)

	l := heap.NewList()
	assert.False(l.Contains(1))
	l = l.Insert(1)
	assert.True(l.Contains(1))
	assert.False(l.Contains(2))

	l = l.Insert(3)
	l = l.Insert(1)

	assert.True(l.Contains(1), "re-inserted element")
	assert.True(l.Contains(3))
}

func TestLinkedListDelete(t *testing.T) {
	assert := assert.New(t)

	l := heap.NewList()
	l = l.Insert(1)
	l = l.Insert(2)
	l = l.Insert(4)
	l = l.Insert(1)
	l = l.Delete(2)
	assert.True(l.Contains(4))
	assert.True(l.Contains(1))

	l = l.Delete(1)
	assert.False(l.Contains(1), "delete double-inserted element")

	// delete non-existent element
	l = l.Delete(3)
	assert.True(l.Contains(4))
}

func TestLinkedListAppend(t *testing.T) {
	assert := assert.New(t)

	l1 := heap.NewList()
	l1 = l1.Insert(1)
	l1 = l1.Insert(2)

	l2 := heap.NewList()
	l2 = l2.Insert(3)
	l2 = l2.Insert(4)

	l3 := l1.Append(l2)
	for _, elem := range []uint64{1, 2, 3, 4} {
		assert.True(l3.Contains(elem), "missing %d", elem)
	}

	l3 = l3.Insert(5)
	assert.True(l3.Contains(5))
}
