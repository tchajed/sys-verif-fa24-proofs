package concurrent

import "sync"

func SetX(x *uint64) {
	*x = 1
}

func NoGo() {
	var x uint64
	SetX(&x)
}

func FirstGo() {
	var x uint64
	go func() {
		SetX(&x)
	}()
}

func FirstLock() uint64 {
	var x uint64
	m := new(sync.Mutex)
	go func() {
		m.Lock()
		x = 1
		m.Unlock()
	}()
	m.Lock()
	y := x
	m.Unlock()
	return y
}

func LockedCounter() uint64 {
	counter := new(uint64)
	m := new(sync.Mutex)
	go func() {
		m.Lock()
		*counter = *counter + 2
		m.Unlock()
	}()
	go func() {
		m.Lock()
		*counter = *counter + 2
		m.Unlock()
	}()
	m.Lock()
	y := *counter
	m.Unlock()
	return y
}
