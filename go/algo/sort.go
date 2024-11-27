package algo

type Person struct {
	Name string
	Age  uint64
}

// Sort sorts arr by increasing Age.
func Sort(arr []Person) {
	// Bubble sort arr in-place
	l := uint64(len(arr))
	l_m_1 := l - 1
	for i := uint64(0); i < l; i++ {
		for j := uint64(0); j < l_m_1; j++ {
			if arr[j].Age > arr[j+1].Age {
				tmp := arr[j]
				arr[j] = arr[j+1]
				arr[j+1] = tmp
			}
		}
	}
}
