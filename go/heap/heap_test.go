package heap

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestUseIgnoreOneLocOwnership(t *testing.T) {
	UseIgnoreOneLocOwnership()
}

func TestInsert(t *testing.T) {
	assert := assert.New(t)

	// Create a new search tree
	tree := NewSearchTree()

	// Insert some keys into the tree
	tree = tree.Insert(3)
	tree = tree.Insert(7)
	tree = tree.Insert(2)
	tree = tree.Insert(4)
	tree = tree.Insert(6)
	tree = tree.Insert(8)

	// Check if the keys are present in the tree
	assert.True(tree.Contains(3), "Tree should contain key 3")
	assert.True(tree.Contains(7), "Tree should contain key 7")
	assert.True(tree.Contains(2), "Tree should contain key 2")
	assert.True(tree.Contains(4), "Tree should contain key 4")
	assert.True(tree.Contains(6), "Tree should contain key 6")
	assert.True(tree.Contains(8), "Tree should contain key 8")

	// Check if some non-existent keys are not present in the tree
	assert.False(tree.Contains(1), "Tree should not contain key 1")
	assert.False(tree.Contains(9), "Tree should not contain key 9")
}
