package heap

type Node struct {
	elem uint64
	next *Node
}

func NewList() *Node {
	// NOTE: need a variable to workaround a goose bug with the "nil"
	// constant
	var l *Node
	return l
}

func (l *Node) Insert(elem uint64) *Node {
	return &Node{elem: elem, next: l}
}

func (l *Node) Pop() (uint64, *Node, bool) {
	if l == nil {
		return 0, l, false
	}
	return l.elem, l.next, true
}

func (l *Node) Contains(elem uint64) bool {
	var n = l
	var found = false
	for {
		if n == nil {
			break
		}
		if n.elem == elem {
			found = true
			break
		}
		n = n.next
	}
	return found
}

func (l *Node) Delete(elem uint64) *Node {
	if l == nil {
		return l
	}
	if l.elem == elem {
		// recurse to delete any copies
		return l.next.Delete(elem)
	}
	l.next = l.next.Delete(elem)
	return l
}

func (l *Node) Append(other *Node) *Node {
	if l == nil {
		return other
	}
	return &Node{elem: l.elem, next: l.next.Append(other)}
}
