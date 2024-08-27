package heap

type Stack struct {
	elements []uint64
}

func NewStack() *Stack {
	return &Stack{
		elements: []uint64{},
	}
}

func (s *Stack) Push(x uint64) {
	s.elements = append(s.elements, x)
}

// Pop returns the most recently pushed element. The boolean indicates success,
// which is false if the stack was empty.
func (s *Stack) Pop() (uint64, bool) {
	if len(s.elements) == 0 {
		return 0, false
	}
	x := s.elements[len(s.elements)-1]
	s.elements = s.elements[:len(s.elements)-1]
	return x, true
}

type Queue struct {
	back  *Stack
	front *Stack
}

func NewQueue() Queue {
	return Queue{
		back:  NewStack(),
		front: NewStack(),
	}
}

func (q Queue) Push(x uint64) {
	q.back.Push(x)
}

func (q Queue) emptyBack() {
	for {
		x, ok := q.back.Pop()
		if ok {
			q.front.Push(x)
		} else {
			break
		}
	}
}

func (q Queue) Pop() (uint64, bool) {
	x, ok := q.front.Pop()
	if ok {
		return x, true
	}
	q.emptyBack()
	x, ok2 := q.front.Pop()
	return x, ok2
}
