package functional

import "github.com/goose-lang/std"

// Add returns the sum of a and b
func Add(a uint64, b uint64) uint64 {
	return a + b
}

// Max returns the max of a and b
func Max(a uint64, b uint64) uint64 {
	if a > b {
		return a
	}
	return b
}

func Midpoint(x, y uint64) uint64 {
	return (x + y) / 2
}

// Midpoint2 calculates the midpoint in an overflow-proof way
func Midpoint2(x, y uint64) uint64 {
	return x + (y-x)/2
}

func Arith(a, b uint64) uint64 {
	sum := a + b
	if sum == 7 {
		return a
	}
	mid := Midpoint(a, b)
	return mid
}

// SumNrec adds up the numbers from 1 to n, recursively.
func SumNrec(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return n + SumNrec(n-1)
}

// SumN adds up the numbers from 1 to n, with a loop.
func SumN(n uint64) uint64 {
	var sum = uint64(0)
	var i = uint64(1)
	for {
		if i > n {
			break
		}
		sum = std.SumAssumeNoOverflow(sum, i)
		i++
	}
	return sum
}

// Fibonacci returns the nth Fibonacci number
func Fibonacci(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	var fib_prev = uint64(0)
	var fib_cur = uint64(1)
	for i := uint64(1); i < n; i++ {
		fib_next := fib_cur + fib_prev
		fib_prev = fib_cur
		fib_cur = fib_next
	}
	return fib_cur
}

// Factorial returns n factorial
func Factorial(n uint64) uint64 {
	if n == 0 {
		return 1
	}
	var fact = uint64(1)
	// NOTE: looping from 0 to n is easier for Goose, though a loop from 1 to i <=
	// n might be more natural
	for i := uint64(0); i < n; i++ {
		fact = fact * (i + 1)
	}
	return fact
}

// FastExp returns b to the power of n0
func FastExp(b uint64, n0 uint64) uint64 {
	var a uint64 = 1
	var c = b
	var n = n0
	for n > 0 {
		if n%2 == 1 {
			a = a * c
			n = n / 2
		} else {
			n = n / 2
		}
		c = c * c
	}
	return a
}
