package memoize

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestMemoize(t *testing.T) {
	assert := assert.New(t)
	m := NewMemoize(func(x uint64) uint64 { return x * x })
	assert.Equal(uint64(9), m.Call(3))
	assert.Equal(uint64(9), m.Call(3))

	assert.Equal(uint64(1), m.Call(1))
	assert.Equal(uint64(4), m.Call(2))
	assert.Equal(uint64(1), m.Call(1))
}

func TestMockMemoize(t *testing.T) {
	assert := assert.New(t)
	m := NewMockMemoize(func(x uint64) uint64 { return x * x })
	assert.Equal(uint64(9), m.Call(3))
	assert.Equal(uint64(9), m.Call(3))

	assert.Equal(uint64(1), m.Call(1))
	assert.Equal(uint64(4), m.Call(2))
	assert.Equal(uint64(1), m.Call(1))
}

func TestMemoizeClient1(t *testing.T) {
	UseMemoize1()
}

func TestMemoizeClient2(t *testing.T) {
	s := []uint64{123, 1, 100, 66, 89}
	UseMemoize2(s)
}
