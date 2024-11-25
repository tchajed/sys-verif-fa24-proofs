package sharded_hashmap

// this file implements a version of shard that doesn't use a map but provides
// the same interface
//
// this turned out to be challenging and uninteresting to verify

type entry struct {
	key uint32
	val uint64
}

type entryShard struct {
	entries []entry
}

func (es *entryShard) Get(key uint32) (uint64, bool) {
	entries := es.entries
	var found = false
	var val = uint64(0)
	var i = uint64(0)
	for i < uint64(len(entries)) {
		e := entries[i]
		if e.key == key {
			found = true
			val = e.val
			break
		}
		i++
	}
	return val, found
}

func (es *entryShard) Store(key uint32, val uint64) {
	var found = false
	var i = uint64(0)
	l := uint64(len(es.entries))
	for i < l {
		if es.entries[i].key == key {
			found = true
			break
		}
		i++
	}
	if found {
		es.entries[i] = entry{key: key, val: val}
	} else {
		es.entries = append(es.entries, entry{key: key, val: val})
	}
}
