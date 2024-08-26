package heap

func Swap(x *uint64, y *uint64) {
	old_y := *y
	*y = *x
	*x = old_y
}
