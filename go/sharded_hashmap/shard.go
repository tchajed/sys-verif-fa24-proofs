package sharded_hashmap

// A small library that logically implements a map from uint32 to uint64; this
// version uses a Go map (from uint64 due to Goose limitations), while the
// alternative in entries.go uses a slice of entries.
//
// This is used within each bucket and protected by a lock, so it does not need
// to be thread safe.

// A shard is logically a map from uint32 to uint64. It is not safe for
// concurrent use.
type shard struct {
	// we use a map from uint64 due to a goose limitation
	m map[uint64]uint64
}

func newShard() *shard {
	return &shard{m: make(map[uint64]uint64)}
}

func (s *shard) Load(key uint32) (uint64, bool) {
	v, ok := s.m[uint64(key)]
	return v, ok
}

func (s *shard) Store(key uint32, v uint64) {
	s.m[uint64(key)] = v
}
