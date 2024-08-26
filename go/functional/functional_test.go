package functional

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func fibRecursive(n uint64) uint64 {
	if n <= 1 {
		return n
	}
	return fibRecursive(n-1) + fibRecursive(n-2)
}

func TestFibonacci(t *testing.T) {
	assert := assert.New(t)
	tests := []struct {
		n        uint64
		expected uint64
	}{
		{0, 0},
		{1, 1},
		{2, 1},
		{3, 2},
		{4, 3},
		{5, 5},
		{6, 8},
		{7, 13},
		{8, 21},
		{9, 34},
	}

	for _, test := range tests {
		result := Fibonacci(test.n)
		assert.Equal(test.expected, result, "Fibonacci(%d) = %d", test.n)
		assert.Equal(fibRecursive(test.n), result, "Fibonacci(%d) = %d", test.n)
	}
}
func TestFactorial(t *testing.T) {
	assert := assert.New(t)
	tests := []struct {
		n        uint64
		expected uint64
	}{
		{0, 1},
		{1, 1},
		{2, 2},
		{3, 6},
		{4, 24},
		{5, 120},
		{6, 720},
		{7, 5040},
		{8, 40320},
		{9, 362880},
	}

	for _, test := range tests {
		result := Factorial(test.n)
		assert.Equal(test.expected, result, "Factorial(%d) = %d", test.n, test.expected)
	}
}

func specExp(b uint64, n uint64) uint64 {
	if n == 0 {
		return 1
	}
	return b * specExp(b, n-1)
}

func TestSpecExp(t *testing.T) {
	// easy-to-read sanity check, without any table-driven tests
	assert.Equal(t, uint64(9), specExp(3, 2))
}

func TestFastExp(t *testing.T) {
	assert := assert.New(t)

	tests := []struct {
		b        uint64
		n        uint64
		expected uint64
	}{
		{2, 0, 1},
		{2, 1, 2},
		{2, 2, 4},
		{2, 3, 8},
		{2, 4, 16},
		{3, 0, 1},
		{3, 1, 3},
		{3, 2, 9},
		{3, 3, 27},
		{3, 4, 81},
	}

	for _, test := range tests {
		result := FastExp(test.b, test.n)
		assert.Equal(test.expected, result, "FastExp(%d, %d)", test.b, test.n)
		assert.Equal(specExp(test.b, test.n), result, "FastExp(%d, %d)", test.b, test.n)
	}
}
