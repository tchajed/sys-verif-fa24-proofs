package heap

type SearchTree struct {
	key   uint64
	left  *SearchTree
	right *SearchTree
}

func NewSearchTree() *SearchTree {
	// NOTE: this pattern works around a Goose bug with translating the nil
	// constant
	var s *SearchTree
	return s
}

func singletonTree(key uint64) *SearchTree {
	// NOTE: same workaround for Goose bug
	var s *SearchTree
	return &SearchTree{key: key, left: s, right: s}
}

func (t *SearchTree) Insert(key uint64) *SearchTree {
	if t == nil {
		return singletonTree(key)
	}
	// modify in-place
	if key < t.key {
		t.left = t.left.Insert(key)
	} else if t.key < key {
		t.right = t.right.Insert(key)
	}
	// if t.Key == key then key is already present
	return t
}

func (t *SearchTree) Contains(key uint64) bool {
	if t == nil {
		return false
	}
	if key == t.key {
		return true
	}
	if key < t.key {
		return t.left.Contains(key)
	}
	return t.right.Contains(key)
}
