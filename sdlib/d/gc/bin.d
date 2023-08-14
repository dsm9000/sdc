module d.gc.bin;

import d.gc.arena;
import d.gc.emap;
import d.gc.spec;

enum InvalidBinID = 0xff;

/**
 * A bin is used to keep track of runs of a certain
 * size class. There is one bin per small size class.
 */
struct Bin {
	import d.sync.mutex;
	shared Mutex mutex;

	import d.gc.extent;
	Extent* current;

	// XXX: We might want to consider targeting Extents
	// on old huge pages instead of just address.
	import d.gc.heap;
	Heap!(Extent, addrExtentCmp) slabs;

	void* alloc(shared(Arena)* arena, shared(ExtentMap)* emap, ubyte sizeClass,
	            bool isAppendable, bool isFinalizable) shared {
		assert(sizeClass < ClassCount.Small);
		assert(&arena.bins[sizeClass] == &this, "Invalid arena or sizeClass!");

		// Load eagerly as prefetching.
		auto size = binInfos[sizeClass].itemSize;

		Extent* slab;
		uint index;

		{
			mutex.lock();
			scope(exit) mutex.unlock();

			slab = (cast(Bin*) &this).getSlab(arena, emap, sizeClass);
			if (slab is null) {
				return null;
			}

			index = slab.allocate(isAppendable, isFinalizable);
		}

		return slab.address + index * size;
	}

	bool free(shared(Arena)* arena, void* ptr, PageDescriptor pd) shared {
		assert(pd.extent !is null, "Extent is null!");
		assert(pd.isSlab(), "Expected a slab!");
		assert(pd.extent.contains(ptr), "ptr not in slab!");
		assert(&arena.bins[pd.sizeClass] == &this,
		       "Invalid arena or sizeClass!");

		auto e = pd.extent;
		auto sc = pd.sizeClass;

		import d.gc.util;
		auto offset = alignDownOffset(ptr, PageSize) + pd.index * PageSize;
		auto index = binInfos[sc].computeIndex(offset);
		auto slots = binInfos[sc].slots;

		auto base = ptr - offset;
		assert(ptr is base + index * binInfos[sc].itemSize);

		mutex.lock();
		scope(exit) mutex.unlock();

		return (cast(Bin*) &this).freeImpl(e, index, slots);
	}

private:
	bool freeImpl(Extent* e, uint index, uint slots) {
		// FIXME: in contract.
		assert(mutex.isHeld(), "Mutex not held!");

		e.free(index);

		auto nfree = e.freeSlots;
		if (nfree == slots) {
			if (e is current) {
				current = null;
				return true;
			}

			// If we only had one slot, we never got added to the heap.
			if (slots > 1) {
				slabs.remove(e);
			}

			return true;
		}

		if (nfree == 1 && e !is current) {
			// Newly non empty.
			assert(slots > 1);
			slabs.insert(e);
		}

		return false;
	}

	auto tryGetSlab() {
		// FIXME: in contract.
		assert(mutex.isHeld(), "Mutex not held!");

		// If the current slab still have free slots, go for it.
		if (current !is null && current.freeSlots != 0) {
			return current;
		}

		current = slabs.pop();
		return current;
	}

	auto getSlab(shared(Arena)* arena, shared(ExtentMap)* emap,
	             ubyte sizeClass) {
		// FIXME: in contract.
		assert(mutex.isHeld(), "Mutex not held!");

		auto slab = tryGetSlab();
		if (slab !is null) {
			return slab;
		}

		{
			// Release the lock while we allocate a slab.
			mutex.unlock();
			scope(exit) mutex.lock();

			// We don't have a suitable slab, so allocate one.
			slab = arena.allocSlab(emap, sizeClass);
		}

		if (slab is null) {
			// Another thread might have been successful
			// while we did not hold the lock.
			return tryGetSlab();
		}

		// We may have allocated the slab we need when the lock was released.
		if (current is null || current.freeSlots == 0) {
			current = slab;
			return slab;
		}

		// If we have, then free the run we just allocated.
		assert(slab !is current);
		assert(current.freeSlots > 0);

		// In which case we put the free run back in the tree.
		assert(slab.freeSlots == binInfos[sizeClass].slots);
		arena.freeSlab(emap, slab);

		// And use the metadata run.
		return current;
	}
}

struct BinInfo {
	ushort itemSize;
	ushort slots;
	ubyte needPages;
	ubyte shift;
	ushort mul;

	this(ushort itemSize, ubyte shift, ubyte needPages, ushort slots) {
		this.itemSize = itemSize;
		this.slots = slots;
		this.needPages = needPages;
		this.shift = (shift + 17) & 0xff;

		// XXX: out contract
		enum MaxShiftMask = (8 * size_t.sizeof) - 1;
		assert(this.shift == (this.shift & MaxShiftMask));

		/**
		 * This is a bunch of magic values used to avoid requiring
		 * division to find the index of an item within a run.
		 *
		 * Computed using finddivisor.d
		 */
		ushort[4] mulIndices = [32768, 26215, 21846, 18725];
		auto tag = (itemSize >> shift) & 0x03;
		this.mul = mulIndices[tag];
	}

	uint computeIndex(size_t offset) const {
		// FIXME: in contract.
		assert(offset < needPages * PageSize, "Offset out of bounds!");

		return cast(uint) ((offset * mul) >> shift);
	}
}

// Determine whether given size class may hold appendability flag.
bool mayAppend(ubyte sizeClass) {
	return !isSmall(sizeClass) || (binInfos[sizeClass].slots <= 256);
}

// Determine whether given size class may hold finalization flag.
bool mayFinalize(ubyte sizeClass) {
	return !isSmall(sizeClass) || (binInfos[sizeClass].slots <= 128);
}

// Take given alloc size and augment if required to store the given meta flags.
// Size class may transition from small (slab) alloc to large in this process.
size_t sizeUpWithMeta(size_t size, bool append, bool finalize) {
	auto sc = getSizeClass(size);
	while ((append && !mayAppend(sc)) || (finalize && !mayFinalize(sc))) {
		sc += 1;
		assert(sc <= ubyte.max);
	}

	return getSizeFromClass(sc);
}

unittest sizeClassForMeta {
	assert(!mayAppend(0));
	assert(!mayFinalize(0));
	assert(mayAppend(1));
	assert(!mayFinalize(1));
	assert(!mayAppend(2));
	assert(!mayFinalize(2));
	assert(mayAppend(3));
	assert(mayFinalize(3));
	assert(mayAppend(11));
	assert(mayFinalize(11));
	assert(sizeUpWithMeta(1, false, false) == 8);
	assert(sizeUpWithMeta(1, true, false) == 16);
	assert(sizeUpWithMeta(1, false, true) == 32);
	assert(sizeUpWithMeta(39, true, false) == 48);
	assert(sizeUpWithMeta(39, false, true) == 64);
	assert(sizeUpWithMeta(50, false, false) == 56);
	assert(sizeUpWithMeta(50, true, false) == 64);
}

// Determine effective size required for an alloc (presumed initially to be
// small, i.e. on slab) with given payload length and set of meta flags.
// If the initial size is not small, it is returned unchanged.
// The returned effective size is not guaranteed to be small;
// calling code must verify whether the alloc may still take place on slab.
size_t effectiveSizeWithMeta(size_t payloadSize, bool isAppendable,
                             bool isFinalizable) {
	auto size = payloadSize;
	// Find initial estimate for size class, assuming smallness:
	auto lenBytes = size < 256 ? 1 : 2; // init estimate for length bytes
	auto finBytes = isFinalizable ? 8 : 0; // room for void* if finalized
	auto trySize = size + lenBytes + finBytes;
	if (trySize <= SizeClass.Small) {
		// Ensure that we have a size class that allows our meta flags:
		trySize = sizeUpWithMeta(trySize, isAppendable, isFinalizable);
		// May need to recalculate size class if crossed 256 bytes :
		if ((lenBytes == 1) && (trySize >= 256)) {
			trySize += 1; // Now need extra byte for length header
			trySize = sizeUpWithMeta(trySize, isAppendable, isFinalizable);
		}

		size = trySize; // Effective size
	}

	return size;
}

unittest effectiveSizeWithMeta {
	assert(effectiveSizeWithMeta(7, false, false) == 8);
	assert(effectiveSizeWithMeta(1, true, false) == 16);
}

import d.gc.sizeclass;
immutable BinInfo[ClassCount.Small] binInfos = getBinInfos();
