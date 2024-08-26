//go:build !goose

package algo

type Edge struct {
	Src uint32
	Dst uint32
}

type Graph struct {
	Edges []Edge
	Nodes []uint32
}

func NewGraph(edges []Edge) Graph {
	node_map := make(map[uint32]struct{}, 0)
	for _, e := range edges {
		node_map[e.Src] = struct{}{}
		node_map[e.Dst] = struct{}{}
	}

	var nodes = make([]uint32, 0, len(node_map))
	for n := range node_map {
		nodes = append(nodes, n)
	}

	return Graph{Edges: edges, Nodes: nodes}
}

func isSource(graph Graph, v uint32) bool {
	for _, e := range graph.Edges {
		if e.Dst == v {
			return false
		}
	}
	return true
}

func initSources(graph Graph) []uint32 {
	var sources = []uint32{}
	for _, n := range graph.Nodes {
		if isSource(graph, n) {
			sources = append(sources, n)
		}
	}
	return sources
}

func findSucc(graph Graph, u uint32) (uint64, bool) {
	for i, e := range graph.Edges {
		if e.Src == u {
			return uint64(i), true
		}
	}
	return 0, false
}

func TopoSort(graph Graph) []uint32 {
	var order = []uint32{}
	var sources = initSources(graph)

	for len(sources) > 0 {
		u := sources[0]
		sources = sources[1:]
		order = append(order, u)
		for {
			e_i, ok := findSucc(graph, u)
			if !ok {
				break
			}
			v := graph.Edges[e_i].Dst
			graph.Edges = append(graph.Edges[:e_i], graph.Edges[e_i+1:]...)
			if isSource(graph, v) {
				sources = append(sources, v)
			}
		}
	}

	return order
}
