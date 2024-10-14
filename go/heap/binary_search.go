package heap

// BinarySearch looks for needle in the sorted list s. It returns (index, found)
// where if found = false, needle is not present in s, and if found = true, s[index]
// == needle.
//
// If needle appears multiple times in s, no guarantees are made about which of
// those indices is returned.
func BinarySearch(s []uint64, needle uint64) (uint64, bool) {
	var i = uint64(0)
	var j = uint64(len(s))
	for i < j {
		mid := i + (j-i)/2
		if s[mid] < needle {
			i = mid + 1
		} else {
			j = mid
		}
	}
	if i < uint64(len(s)) {
		return i, s[i] == needle
	}
	return i, false
}
