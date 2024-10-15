package heap

// FindMajority finds an `x` that appears in the slice `a` more than half the
// time.
//
// That is, if there is some x that appears in a strictly more than `len(a)/2`
// times, then `FindMajority` will return it.
//
// This implementation of the algorithm comes from _Program Proofs_ by K. Rustan
// M. Leino in chapter 13.7.
func FindMajority[T comparable](a []T) T {
	var k = a[0]
	var lo = uint64(0)
	var hi = uint64(1)
	var c = uint64(1)
	l := uint64(len(a))
	for hi < l {
		if a[hi] == k {
			// hi, c = hi+1, c+1
			hi++
			c++
		} else if hi+1-lo < 2*c {
			hi++
		} else {
			hi++
		}
		if hi == l {
			// return k
			break
		}
		// k, lo, hi, c = a[hi], hi, hi+1, 1
		k = a[hi]
		lo = hi
		hi++
		c = 1
	}
	return k
}
