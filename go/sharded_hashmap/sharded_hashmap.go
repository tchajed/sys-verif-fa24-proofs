package sharded_hashmap

import (
	"sync"
)

func hash(key uint32) uint32 {
	// https://stackoverflow.com/questions/7666509/hash-function-for-string
	// djb2 but multiply by 17000069 rather than 33
	var h = uint32(5381)
	k := uint32(17000069)
	h = (h * k) + (key & 0xff)
	h = (h * k) + ((key >> 8) & 0xff)
	h = (h * k) + ((key >> 16) & 0xff)
	h = (h * k) + ((key >> 24) & 0xff)
	return h
}

type bucket struct {
	mu     *sync.Mutex
	subMap *shard
}

type HashMap struct {
	buckets []*bucket
}

func newBucket() *bucket {
	return &bucket{
		mu:     new(sync.Mutex),
		subMap: newShard(),
	}
}

func createNewBuckets(newSize uint32) []*bucket {
	var newBuckets = []*bucket{}
	numBuckets := uint64(newSize)
	for i := uint64(0); i < numBuckets; i++ {
		newBuckets = append(newBuckets, newBucket())
	}
	return newBuckets
}

func NewHashMap(size uint32) *HashMap {
	return &HashMap{
		buckets: createNewBuckets(size),
	}
}

func bucketIdx(key uint32, numBuckets uint64) uint64 {
	return uint64(hash(key) % uint32(numBuckets))
}

func (hm *HashMap) Load(key uint32) (uint64, bool) {
	buckets := hm.buckets
	b := buckets[bucketIdx(key, uint64(len(buckets)))]
	b.mu.Lock()
	x, ok := b.subMap.Load(key)
	b.mu.Unlock()
	return x, ok
}

func (hm *HashMap) Store(key uint32, val uint64) {
	buckets := hm.buckets
	b := buckets[bucketIdx(key, uint64(len(buckets)))]
	b.mu.Lock()
	b.subMap.Store(key, val)
	b.mu.Unlock()
}
