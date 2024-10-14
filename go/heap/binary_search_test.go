package heap

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestBinarySearch(t *testing.T) {
	assert := assert.New(t)

	s := []uint64{1, 3, 4, 5}
	var i uint64
	var ok bool
	i, ok = BinarySearch(s, 2)
	assert.False(ok)

	i, ok = BinarySearch(s, 1)
	assert.Equal(uint64(0), i)
	assert.True(ok)

	i, ok = BinarySearch(s, 5)
	assert.Equal(uint64(3), i)
	assert.True(ok)

	i, ok = BinarySearch(s, 6)
	assert.False(ok)
}
