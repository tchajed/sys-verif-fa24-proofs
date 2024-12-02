package algo_test

import (
	"slices"
	"testing"

	"github.com/stretchr/testify/assert"
	"pgregory.net/rapid"
	"sys_verif_code/algo"
)

func isLeaf(graph algo.Graph, v uint32) bool {
	for _, e := range graph.Edges {
		if e.Src == v {
			return false
		}
	}
	return true
}

func findLeaf(graph algo.Graph) (uint32, bool) {
	for _, n := range graph.Nodes {
		if isLeaf(graph, n) {
			return n, true
		}
	}
	return 0, false
}

func removeNode(graph *algo.Graph, v uint32) {
	graph.Nodes = slices.DeleteFunc(graph.Nodes, func(n uint32) bool {
		return n == v
	})
	graph.Edges = slices.DeleteFunc(graph.Edges, func(e algo.Edge) bool {
		return e.Src == v || e.Dst == v
	})
}

func isAcyclic(graph algo.Graph) bool {
	graph = algo.Graph{
		Edges: slices.Clone(graph.Edges),
		Nodes: slices.Clone(graph.Nodes),
	}
	for {
		v, ok := findLeaf(graph)
		if !ok {
			break
		}
		removeNode(&graph, v)
	}
	return len(graph.Nodes) == 0
}

func TestAcyclic(t *testing.T) {
	g := algo.NewGraph([]algo.Edge{{0, 1}, {1, 2}, {2, 0}})
	assert.False(t, isAcyclic(g))

	g = algo.NewGraph([]algo.Edge{{0, 1}, {1, 2}, {2, 3}})
	num_nodes := len(g.Nodes)
	assert.True(t, isAcyclic(g))
	// sanity check isAcyclic does not modify its input
	assert.Len(t, g.Nodes, num_nodes, "number of nodes changed")

	g = algo.NewGraph([]algo.Edge{{0, 0}, {1, 2}})
	assert.False(t, isAcyclic(g))
}

func GraphGenerator() *rapid.Generator[algo.Graph] {
	return rapid.Custom(func(t *rapid.T) algo.Graph {
		edges := rapid.SliceOfN(rapid.Custom(func(t *rapid.T) algo.Edge {
			// make sure node numbers are small to make it easier to have interesting graph structure
			num_nodes := rapid.Uint32Range(3, 10).Draw(t, "num_nodes")
			return algo.Edge{
				Src: rapid.Uint32Range(1, num_nodes).Draw(t, "src"),
				Dst: rapid.Uint32Range(1, num_nodes).Draw(t, "dst"),
			}
		}), 0, 25).Draw(t, "edges")
		return algo.NewGraph(edges)
	})
}

func TestTopoSortProperties(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		assert := assert.New(t)
		g := GraphGenerator().Filter(func(g algo.Graph) bool {
			// graph must be acyclic
			return isAcyclic(g)
		}).Draw(t, "g")
		order := algo.TopoSort(g)
		if assert.ElementsMatch(g.Nodes, order) {
			for _, e := range g.Edges {
				// indices will be valid since elements match
				assert.Less(
					slices.Index(order, e.Src),
					slices.Index(order, e.Dst),
					"graph ordering not followed",
				)
			}
		}
	})
}
