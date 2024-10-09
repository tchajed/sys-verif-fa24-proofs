package heap

import "github.com/goose-lang/primitive"

func Swap(x *uint64, y *uint64) {
	old_y := *y
	*y = *x
	*x = old_y
}

// IgnoreOneLocF has a specification that shows it does not need ownership of
// its second argument.
func IgnoreOneLocF(x *uint64, y *uint64) {
	primitive.Assert(*x == 0)
	*x = 42
}

// UseIgnoreOneLocOwnership uses IgnoreOneLocF and can be verified using its
// specification.
func UseIgnoreOneLocOwnership() {
	var x = uint64(0)
	var y = uint64(42)
	IgnoreOneLocF(&x, &y)
	primitive.Assert(x == y)
}

// CopySlice copies from src to dst
//
// dst must be at least as long as src
func CopySlice(dst []byte, src []byte) {
	l := uint64(len(dst))
	for i := uint64(0); i < l; i++ {
		dst[i] = src[i]
	}
}

func StackEscape() *uint64 {
	var x = uint64(42)
	return &x
}
