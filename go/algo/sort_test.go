package algo_test

import (
	"slices"
	"sort"
	"testing"

	"sys_verif_code/algo"

	"github.com/stretchr/testify/assert"
	"pgregory.net/rapid"
)

func TestSortSanity(t *testing.T) {
	assert := assert.New(t)

	arr := []algo.Person{
		{"Alice", 25},
		{"Bob", 20},
		{"Charlie", 30},
	}

	algo.Sort(arr)
	assert.Equal([]algo.Person{
		{"Bob", 20},
		{"Alice", 25},
		{"Charlie", 30},
	}, arr)
}

func TestSortEmpty(t *testing.T) {
	arr := []algo.Person{}
	algo.Sort(arr)
	assert.Equal(t, arr, []algo.Person{})
}

// var PersonGenerator *rapid.Generator[algo.Person] = rapid.Custom(func(t *rapid.T) algo.Person {
// 	return algo.Person{
// 		Name: rapid.String().Draw(t, "name"),
// 		Age:  rapid.Uint64().Draw(t, "age"),
// 	}
// })

func TestSortProperties(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		assert := assert.New(t)
		arr := rapid.SliceOf(rapid.Make[algo.Person]()).Draw(t, "arr")

		input := slices.Clone(arr)
		algo.Sort(arr)

		// we'll defer to assert's elements matcher and the standard library sort
		// checker, rather than implementing these ourselves
		assert.Len(arr, len(input))
		assert.ElementsMatch(arr, input)
		assert.True(sort.SliceIsSorted(arr, func(i, j int) bool {
			return arr[i].Age < arr[j].Age
		}), "arr is not sorted")
	})
}
