package heap

import "github.com/goose-lang/primitive"

func ExampleA(x *bool, y *uint64, z uint64) {
	if *x {
		*y = z
	} else {
		*y = 0
	}
}

func ExampleB(x *bool, y *uint64, z uint64) {
	if *x {
		primitive.Assert(z == 0)
		*y = z
	} else {
		*y = 0
	}
}

type S1 struct {
	a uint64
	b []byte
}

func ExampleC(x *S1) string {
	return "unimplemented"
}

func ExampleD(x *S1) string {
	if x.a == 0 {
		return "false"
	}
	return "true"
}

func ExampleE(x *S1) byte {
	primitive.Assert(x.a == uint64(len(x.b)))
	return x.b[0]
}

func ExampleF(x S1, y *S1) {
	y.a = x.a
	y.b = nil
}

func collatzF(x uint64) uint64 {
	if x%2 == 0 {
		return x / 2
	} else {
		return 3*x + 1
	}
}

func collatzIter(x uint64, n uint64) uint64 {
	if n == 0 {
		return x
	} else {
		return collatzIter(collatzF(x), n-1)
	}
}

func ExampleG() uint64 {
	return collatzIter(12, 9)
}
