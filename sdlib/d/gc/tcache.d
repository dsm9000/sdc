module d.gc.tcache;

import d.gc.base;
import d.gc.emap;
import d.gc.size;
import d.gc.sizeclass;
import d.gc.slab;
import d.gc.spec;
import d.gc.util;

ThreadCache threadCache;

struct ThreadCache {
private:
	CachedExtentMap emap;

public:
	void initialize(shared(ExtentMap)* emap, shared(Base)* base) {
		this.emap = CachedExtentMap(emap, base);
	}

	void* alloc(size_t size, bool containsPointers, bool zero) {
		if (!isAllocatableSize(size)) {
			return null;
		}

		auto arena = chooseArena(containsPointers);
		if (isSmallSize(size)) {
			return arena.allocSmall(emap, size, zero);
		}

		return arena.allocLarge(emap, size, zero);
	}

	void* allocAppendable(size_t size, bool containsPointers, bool zero,
	                      Finalizer finalizer = null) {
		if (!isAllocatableSize(size)) {
			return null;
		}

		auto reservedBytes = finalizer is null ? 0 : PointerSize;
		auto asize = getAllocSize(alignUp(size + reservedBytes, 2 * Quantum));
		assert(sizeClassSupportsMetadata(getSizeClass(asize)),
		       "allocAppendable got size class without metadata support!");

		auto arena = chooseArena(containsPointers);
		if (isSmallSize(asize)) {
			auto ptr = arena.allocSmall(emap, asize, zero);
			auto pd = getPageDescriptor(ptr);
			auto si = SlabAllocInfo(pd, ptr);
			si.initializeMetadata(finalizer, size);
			return ptr;
		}

		auto ptr = arena.allocLarge(emap, size, zero);
		auto pd = getPageDescriptor(ptr);
		auto e = pd.extent;
		e.setUsedCapacity(size);
		e.setFinalizer(finalizer);
		return ptr;
	}

	void free(void* ptr) {
		if (ptr is null) {
			return;
		}

		auto pd = getPageDescriptor(ptr);
		pd.arena.free(emap, pd, ptr);
	}

	void destroy(void* ptr) {
		if (ptr is null) {
			return;
		}

		auto pd = getPageDescriptor(ptr);
		auto e = pd.extent;

		if (pd.isSlab()) {
			auto si = SlabAllocInfo(pd, ptr);
			auto finalizer = si.finalizer;
			if (finalizer !is null) {
				assert(cast(void*) si.address == ptr,
				       "destroy() was invoked on an interior pointer!");

				finalizer(ptr, si.usedCapacity);
			}
		} else {
			if (e.finalizer !is null) {
				e.finalizer(ptr, e.usedCapacity);
			}
		}

		pd.arena.free(emap, pd, ptr);
	}

	void* realloc(void* ptr, size_t size, bool containsPointers) {
		if (size == 0) {
			free(ptr);
			return null;
		}

		if (!isAllocatableSize(size)) {
			return null;
		}

		if (ptr is null) {
			return alloc(size, containsPointers, false);
		}

		auto copySize = size;
		auto pd = getPageDescriptor(ptr);
		auto samePointerness = containsPointers == pd.containsPointers;

		if (pd.isSlab()) {
			auto newSizeClass = getSizeClass(size);
			auto oldSizeClass = pd.sizeClass;
			if (samePointerness && newSizeClass == oldSizeClass) {
				auto si = SlabAllocInfo(pd, ptr);
				if (!si.supportsMetadata || si.setUsedCapacity(size)) {
					return ptr;
				}
			}

			if (newSizeClass > oldSizeClass) {
				copySize = getSizeFromClass(oldSizeClass);
			}
		} else {
			auto esize = pd.extent.size;
			if (samePointerness && (alignUp(size, PageSize) == esize
				    || pd.arena.resizeLarge(emap, pd.extent, size))) {
				pd.extent.setUsedCapacity(size);
				return ptr;
			}

			import d.gc.util;
			copySize = min(size, pd.extent.usedCapacity);
		}

		auto newPtr = alloc(size, containsPointers, false);
		if (newPtr is null) {
			return null;
		}

		if (!isSmallSize(size)) {
			auto npd = getPageDescriptor(newPtr);
			npd.extent.setUsedCapacity(size);
		}

		memcpy(newPtr, ptr, copySize);
		pd.arena.free(emap, pd, ptr);

		return newPtr;
	}

	/**
	 * Appendable facilities.
	 */
	size_t getCapacity(const void[] slice) {
		auto pd = maybeGetPageDescriptor(slice.ptr);
		auto e = pd.extent;
		if (e is null) {
			return 0;
		}

		if (pd.isSlab()) {
			auto si = SlabAllocInfo(pd, slice.ptr);

			if (!validateCapacity(slice, si.address, si.usedCapacity)) {
				return 0;
			}

			auto startIndex = slice.ptr - si.address;
			return si.slotCapacity - startIndex;
		}

		if (!validateCapacity(slice, e.address, e.usedCapacity)) {
			return 0;
		}

		auto startIndex = slice.ptr - e.address;
		return e.size - startIndex;
	}

	bool extend(const void[] slice, size_t size) {
		if (size == 0) {
			return true;
		}

		auto pd = maybeGetPageDescriptor(slice.ptr);
		auto e = pd.extent;

		if (e is null) {
			return false;
		}

		if (pd.isSlab()) {
			auto si = SlabAllocInfo(pd, slice.ptr);
			auto usedCapacity = si.usedCapacity;

			if (!validateCapacity(slice, si.address, usedCapacity)) {
				return false;
			}

			return si.setUsedCapacity(usedCapacity + size);
		}

		if (!validateCapacity(slice, e.address, e.usedCapacity)) {
			return false;
		}

		auto newCapacity = e.usedCapacity + size;
		if ((e.size < newCapacity)
			    && !pd.arena.resizeLarge(emap, e, newCapacity)) {
			return false;
		}

		e.setUsedCapacity(newCapacity);
		return true;
	}

	/**
	 * GC facilities.
	 */
	void runGCCycle() {
		import d.thread;
		__sd_thread_stop_the_world();
		scope(exit) __sd_thread_restart_the_world();

		prepareGCCycle();

		// TODO: The set need a range interface or some other way to iterrate.
		// FIXME: Prepare the GC so it has bitfields for all extent classes.

		// TODO: Call into rt.thread to scan stack/statics.

		// TODO: Scan the roots.

		// TODO: Go on and on until all worklists are empty.

		collect();
	}

	void prepareGCCycle() {
		foreach (i; 0 .. ArenaCount) {
			import d.gc.arena;
			auto a = Arena.getIfInitialized(i);
			if (a !is null) {
				a.prepareGCCycle(emap);
			}
		}
	}

	void collect() {
		foreach (i; 0 .. ArenaCount) {
			import d.gc.arena;
			auto a = Arena.getIfInitialized(i);
			if (a !is null) {
				a.collect(emap);
			}
		}
	}

	bool scan(const(void*)[] range) {
		bool newPtr;
		foreach (ptr; range) {
			enum PtrMask = ~(AddressSpace - 1);
			auto iptr = cast(size_t) ptr;

			if (iptr & PtrMask) {
				// This is not a pointer, move along.
				// TODO: Replace this with a min-max test.
				continue;
			}

			auto pd = maybeGetPageDescriptor(ptr);
			if (pd.extent is null) {
				// We have no mapping there.
				continue;
			}

			// We have something, mark!
			newPtr |= true;

			// FIXME: Mark the extent.
			// FIXME: If the extent may contain pointers,
			// add the base ptr to the worklist.
		}

		return newPtr;
	}

private:
	/**
	 * Appendable's mechanics:
	 * 
	 *  __data__  _____free space_______
	 * /        \/                      \
	 * -----sss s....... ....... ........
	 *      \___________________________/
	 * 	           Capacity is 27
	 * 
	 * If the slice's end doesn't match the used capacity,
	 * then we return 0 in order to force a reallocation
	 * when appending:
	 * 
	 *  ___data____  ____free space_____
	 * /           \/                   \
	 * -----sss s---.... ....... ........
	 *      \___________________________/
	 * 	           Capacity is 0
	 * 
	 * See also: https://dlang.org/spec/arrays.html#capacity-reserve
	 */
	bool validateCapacity(const void[] slice, const void* address,
	                      size_t usedCapacity) {
		// Slice must not end before valid data ends, or capacity is zero.
		// To be appendable, the slice end must match the alloc's used
		// capacity, and the latter may not be zero.
		auto startIndex = slice.ptr - address;
		auto stopIndex = startIndex + slice.length;

		return stopIndex != 0 && stopIndex == usedCapacity;
	}

	auto getPageDescriptor(void* ptr) {
		auto pd = maybeGetPageDescriptor(ptr);
		assert(pd.extent !is null);
		assert(pd.isSlab() || ptr is pd.extent.address);

		return pd;
	}

	auto maybeGetPageDescriptor(const void* ptr) {
		import d.gc.util;
		auto aptr = alignDown(ptr, PageSize);
		return emap.lookup(aptr);
	}

	auto chooseArena(bool containsPointers) {
		/**
		 * We assume this call is cheap.
		 * This is true on modern linux with modern versions
		 * of glibc thanks to rseqs, but we might want to find
		 * an alternative on other systems.
		 */
		import sys.posix.sched;
		int cpuid = sched_getcpu();

		import d.gc.arena;
		return Arena.getOrInitialize((cpuid << 1) | containsPointers);
	}
}

private:

unittest nonAllocatableSizes {
	ThreadCache tc;

	// Prohibited sizes of allocations
	assert(tc.alloc(0, false, false) is null);
	assert(tc.alloc(MaxAllocationSize + 1, false, false) is null);
	assert(tc.allocAppendable(0, false, false) is null);
	assert(tc.allocAppendable(MaxAllocationSize + 1, false, false) is null);
}

unittest zero {
	enum LargeSize = 5 * PageSize;
	enum SmallSize = 8;

	ThreadCache tc;
	tc.initialize(&gExtentMap, &gBase);

	// Check that zeroing large allocations works as expected.
	void* ptr0 = null;
	auto ptr = tc.alloc(LargeSize, false, true);

	// Make sure this isn't the only allocation on the block.
	if (isAligned(ptr, BlockSize)) {
		ptr0 = ptr;
		ptr = tc.alloc(LargeSize, false, true);
	}

	void checkValue(ulong value) {
		auto x = cast(ulong*) ptr;

		foreach (_; 0 .. LargeSize / ulong.sizeof) {
			assert(*x++ == value);
		}
	}

	void setValue(ulong value) {
		auto x = cast(ulong*) ptr;

		foreach (_; 0 .. LargeSize / ulong.sizeof) {
			*x++ = value;
		}

		checkValue(value);
	}

	checkValue(0);
	setValue(0xbadc0ffee0ddf00d);

	// We free and reallocate, we should get the same dirty chunk.
	tc.free(ptr);
	assert(tc.alloc(LargeSize, false, false) is ptr);
	checkValue(0xbadc0ffee0ddf00d);

	// We free and reallocate, but asking for zeroed memory.
	tc.free(ptr);
	assert(tc.alloc(LargeSize, false, true) is ptr);
	checkValue(0);

	// Cleanup after ourselves.
	tc.free(ptr);
	tc.free(ptr0);

	// Now lets check we zero correctly small allocation.
	ptr0 = null;
	ptr = tc.alloc(SmallSize, false, true);

	// Make sure this isn't the only allocation on the block.
	if (isAligned(ptr, BlockSize)) {
		ptr0 = ptr;
		ptr = tc.alloc(SmallSize, false, true);
	}

	auto uptr = cast(ulong*) ptr;
	assert(*uptr == 0);

	*uptr = 0xbadc0ffee0ddf00d;
	assert(*uptr == 0xbadc0ffee0ddf00d);

	// Now free and reallocate, check we get back the same slot.
	tc.free(ptr);
	assert(tc.alloc(SmallSize, false, false) is ptr);
	assert(*uptr == 0xbadc0ffee0ddf00d);

	// We free and reallocate, but asking for zeroed memory.
	tc.free(ptr);
	assert(tc.alloc(SmallSize, false, true) is ptr);
	assert(*uptr == 0);

	// Cleanup after ourselves.
	tc.free(ptr);
	tc.free(ptr0);
}

unittest getCapacity {
	ThreadCache tc;
	tc.initialize(&gExtentMap, &gBase);

	// Non-appendable size class 6 (56 bytes)
	auto nonAppendable = tc.alloc(50, false, false);
	assert(tc.getCapacity(nonAppendable[0 .. 0]) == 0);
	assert(tc.getCapacity(nonAppendable[0 .. 50]) == 0);
	assert(tc.getCapacity(nonAppendable[0 .. 56]) == 56);

	// Capacity of any slice in space unknown to the GC is zero:
	void* nullPtr = null;
	assert(tc.getCapacity(nullPtr[0 .. 0]) == 0);
	assert(tc.getCapacity(nullPtr[0 .. 100]) == 0);

	void* stackPtr = &nullPtr;
	assert(tc.getCapacity(stackPtr[0 .. 0]) == 0);
	assert(tc.getCapacity(stackPtr[0 .. 100]) == 0);

	static size_t tlValue;
	void* tlPtr = &tlValue;
	assert(tc.getCapacity(tlPtr[0 .. 0]) == 0);
	assert(tc.getCapacity(tlPtr[0 .. 100]) == 0);

	void* allocAppendableWithCapacity(size_t size, size_t usedCapacity) {
		auto ptr = tc.allocAppendable(size, false, false);
		assert(ptr !is null);
		auto pd = tc.getPageDescriptor(ptr);
		assert(pd.extent !is null);
		assert(pd.extent.isLarge());
		pd.extent.setUsedCapacity(usedCapacity);
		return ptr;
	}

	// Check capacity for an appendable large GC allocation.
	auto p0 = allocAppendableWithCapacity(16384, 100);

	// p0 is appendable and has the minimum large size.
	// Capacity of segment from p0, length 100 is 16384:
	assert(tc.getCapacity(p0[0 .. 100]) == 16384);
	assert(tc.getCapacity(p0[1 .. 100]) == 16383);
	assert(tc.getCapacity(p0[50 .. 100]) == 16334);
	assert(tc.getCapacity(p0[99 .. 100]) == 16285);
	assert(tc.getCapacity(p0[100 .. 100]) == 16284);

	// If the slice doesn't go the end of the allocated area
	// then the capacity must be 0.
	assert(tc.getCapacity(p0[0 .. 0]) == 0);
	assert(tc.getCapacity(p0[0 .. 1]) == 0);
	assert(tc.getCapacity(p0[0 .. 50]) == 0);
	assert(tc.getCapacity(p0[0 .. 99]) == 0);

	assert(tc.getCapacity(p0[0 .. 99]) == 0);
	assert(tc.getCapacity(p0[1 .. 99]) == 0);
	assert(tc.getCapacity(p0[50 .. 99]) == 0);
	assert(tc.getCapacity(p0[99 .. 99]) == 0);

	// This would almost certainly be a bug in userland,
	// but let's make sure be behave reasonably there.
	assert(tc.getCapacity(p0[0 .. 101]) == 0);
	assert(tc.getCapacity(p0[1 .. 101]) == 0);
	assert(tc.getCapacity(p0[50 .. 101]) == 0);
	assert(tc.getCapacity(p0[100 .. 101]) == 0);
	assert(tc.getCapacity(p0[101 .. 101]) == 0);

	// Realloc.
	auto p1 = tc.allocAppendable(20000, false, false);
	assert(tc.getCapacity(p1[0 .. 19999]) == 0);
	assert(tc.getCapacity(p1[0 .. 20000]) == 20480);
	assert(tc.getCapacity(p1[0 .. 20001]) == 0);

	// Decreasing the size of the allocation
	// should adjust capacity acordingly.
	auto p2 = tc.realloc(p1, 19999, false);
	assert(p2 is p1);

	assert(tc.getCapacity(p2[0 .. 19999]) == 20480);
	assert(tc.getCapacity(p2[0 .. 20000]) == 0);
	assert(tc.getCapacity(p2[0 .. 20001]) == 0);

	// Increasing the size of the allocation increases capacity.
	auto p3 = tc.realloc(p2, 20001, false);
	assert(p3 is p2);

	assert(tc.getCapacity(p3[0 .. 19999]) == 0);
	assert(tc.getCapacity(p3[0 .. 20000]) == 0);
	assert(tc.getCapacity(p3[0 .. 20001]) == 20480);

	// This realloc happens in-place:
	auto p4 = tc.realloc(p3, 16000, false);
	assert(p4 is p3);
	assert(tc.getCapacity(p4[0 .. 16000]) == 16384);

	// This one similarly happens in-place:
	auto p5 = tc.realloc(p4, 20000, false);
	assert(p5 is p4);
	assert(tc.getCapacity(p5[0 .. 20000]) == 20480);

	// Realloc from large to small size class results in new allocation:
	auto p6 = tc.realloc(p5, 100, false);
	assert(p6 !is p5);
}

unittest extendLarge {
	ThreadCache tc;
	tc.initialize(&gExtentMap, &gBase);

	// Non-appendable size class 6 (56 bytes)
	auto nonAppendable = tc.alloc(50, false, false);
	assert(tc.getCapacity(nonAppendable[0 .. 50]) == 0);

	// Attempt to extend a non-appendable (always considered fully occupied)
	assert(!tc.extend(nonAppendable[50 .. 50], 1));
	assert(!tc.extend(nonAppendable[0 .. 0], 1));

	// Extend by zero is permitted even when no capacity:
	assert(tc.extend(nonAppendable[50 .. 50], 0));

	// Extend in space unknown to the GC. Can only extend by zero.
	void* nullPtr = null;
	assert(tc.extend(nullPtr[0 .. 100], 0));
	assert(!tc.extend(nullPtr[0 .. 100], 1));
	assert(!tc.extend(nullPtr[100 .. 100], 1));

	void* stackPtr = &nullPtr;
	assert(tc.extend(stackPtr[0 .. 100], 0));
	assert(!tc.extend(stackPtr[0 .. 100], 1));
	assert(!tc.extend(stackPtr[100 .. 100], 1));

	static size_t tlValue;
	void* tlPtr = &tlValue;
	assert(tc.extend(tlPtr[0 .. 100], 0));
	assert(!tc.extend(tlPtr[0 .. 100], 1));
	assert(!tc.extend(tlPtr[100 .. 100], 1));

	void* allocAppendableWithCapacity(size_t size, size_t usedCapacity) {
		auto ptr = tc.allocAppendable(size, false, false);
		assert(ptr !is null);

		// We make sure we can't reisze the allocation by allocating a dead zone after it.
		import d.gc.size;
		auto deadzone = tc.alloc(MaxSmallSize + 1, false, false);
		if (deadzone !is alignUp(ptr + size, PageSize)) {
			tc.free(deadzone);
			scope(success) tc.free(ptr);
			return allocAppendableWithCapacity(size, usedCapacity);
		}

		auto pd = tc.getPageDescriptor(ptr);
		assert(pd.extent !is null);
		assert(pd.extent.isLarge());
		pd.extent.setUsedCapacity(usedCapacity);
		return ptr;
	}

	// Make an appendable alloc:
	auto p0 = allocAppendableWithCapacity(16384, 100);
	assert(tc.getCapacity(p0[0 .. 100]) == 16384);

	// Attempt to extend valid slices with capacity 0.
	// (See getCapacity tests.)
	assert(tc.extend(p0[0 .. 0], 0));
	assert(!tc.extend(p0[0 .. 0], 50));
	assert(!tc.extend(p0[0 .. 99], 50));
	assert(!tc.extend(p0[1 .. 99], 50));
	assert(!tc.extend(p0[0 .. 50], 50));

	// Extend by size zero is permitted but has no effect:
	assert(tc.extend(p0[100 .. 100], 0));
	assert(tc.extend(p0[0 .. 100], 0));
	assert(tc.getCapacity(p0[0 .. 100]) == 16384);
	assert(tc.extend(p0[50 .. 100], 0));
	assert(tc.getCapacity(p0[50 .. 100]) == 16334);

	// Attempt extend with insufficient space (one byte too many) :
	assert(tc.getCapacity(p0[100 .. 100]) == 16284);
	assert(!tc.extend(p0[0 .. 100], 16285));
	assert(!tc.extend(p0[50 .. 100], 16285));

	// Extending to the limit (one less than above) succeeds:
	assert(tc.extend(p0[50 .. 100], 16284));

	// Now we're full, and can extend only by zero:
	assert(tc.extend(p0[0 .. 16384], 0));
	assert(!tc.extend(p0[0 .. 16384], 1));

	// Unless we clear the deadzone, in which case we can extend again.
	tc.free(p0 + 16384);
	assert(tc.extend(p0[0 .. 16384], 1));
	assert(tc.getCapacity(p0[0 .. 16385]) == 16384 + PageSize);

	// Make another appendable alloc:
	auto p1 = allocAppendableWithCapacity(16384, 100);
	assert(tc.getCapacity(p1[0 .. 100]) == 16384);

	// Valid extend :
	assert(tc.extend(p1[0 .. 100], 50));
	assert(tc.getCapacity(p1[100 .. 150]) == 16284);
	assert(tc.extend(p1[0 .. 150], 0));

	// Capacity of old slice becomes 0:
	assert(tc.getCapacity(p1[0 .. 100]) == 0);

	// The only permitted extend is by 0:
	assert(tc.extend(p1[0 .. 100], 0));

	// Capacity of a slice including the original and the extension:
	assert(tc.getCapacity(p1[0 .. 150]) == 16384);

	// Extend the upper half:
	assert(tc.extend(p1[125 .. 150], 100));
	assert(tc.getCapacity(p1[150 .. 250]) == 16234);

	// Original's capacity becomes 0:
	assert(tc.getCapacity(p1[125 .. 150]) == 0);
	assert(tc.extend(p1[125 .. 150], 0));

	// Capacity of a slice including original and extended:
	assert(tc.extend(p1[125 .. 250], 0));
	assert(tc.getCapacity(p1[125 .. 250]) == 16259);

	// Capacity of earlier slice elongated to cover the extensions :
	assert(tc.getCapacity(p1[0 .. 250]) == 16384);

	// Extend a zero-size slice existing at the start of the free space:
	assert(tc.extend(p1[250 .. 250], 200));
	assert(tc.getCapacity(p1[250 .. 450]) == 16134);

	// Capacity of the old slice is now 0:
	assert(tc.getCapacity(p1[0 .. 250]) == 0);

	// Capacity of a slice which includes the original and the extension:
	assert(tc.getCapacity(p1[0 .. 450]) == 16384);

	// Extend so as to fill up all but one byte of free space:
	assert(tc.extend(p1[0 .. 450], 15933));
	assert(tc.getCapacity(p1[16383 .. 16383]) == 1);

	// Extend, filling up last byte of free space:
	assert(tc.extend(p1[16383 .. 16383], 1));
	assert(tc.getCapacity(p1[0 .. 16384]) == 16384);

	// Attempt to extend, but we're full:
	assert(!tc.extend(p1[0 .. 16384], 1));

	// Extend by size zero still works, though:
	assert(tc.extend(p1[0 .. 16384], 0));
}

unittest extendSmall {
	ThreadCache tc;
	tc.initialize(&gExtentMap, &gBase);

	// Make a small appendable alloc:
	auto s0 = tc.allocAppendable(42, false, false);

	assert(tc.getCapacity(s0[0 .. 42]) == 48);
	assert(tc.extend(s0[0 .. 0], 0));
	assert(!tc.extend(s0[0 .. 0], 10));
	assert(!tc.extend(s0[0 .. 41], 10));
	assert(!tc.extend(s0[1 .. 41], 10));
	assert(!tc.extend(s0[0 .. 20], 10));

	// Extend:
	assert(!tc.extend(s0[0 .. 42], 7));
	assert(!tc.extend(s0[32 .. 42], 7));
	assert(tc.extend(s0[0 .. 42], 3));
	assert(tc.getCapacity(s0[0 .. 45]) == 48);

	// Make another in same size class:
	auto s1 = tc.allocAppendable(42, false, false);
	assert(tc.extend(s1[0 .. 42], 1));
	assert(tc.getCapacity(s1[0 .. 43]) == 48);

	// Make sure first alloc not affected:
	assert(tc.getCapacity(s0[0 .. 45]) == 48);

	// Extend some more:
	assert(tc.getCapacity(s0[0 .. 42]) == 0);
	assert(tc.extend(s0[40 .. 45], 2));
	assert(tc.getCapacity(s0[0 .. 45]) == 0);
	assert(tc.getCapacity(s0[0 .. 47]) == 48);
	assert(!tc.extend(s0[0 .. 47], 2));
	assert(tc.extend(s0[0 .. 47], 1));

	// Decreasing the size of the allocation
	// should adjust capacity acordingly.
	auto s2 = tc.realloc(s0, 42, false);
	assert(s2 is s0);
	assert(tc.getCapacity(s2[0 .. 42]) == 48);

	// Same is true for increasing:
	auto s3 = tc.realloc(s2, 45, false);
	assert(s3 is s2);
	assert(tc.getCapacity(s3[0 .. 45]) == 48);

	// Increase that results in size class change:
	auto s4 = tc.realloc(s3, 70, false);
	assert(s4 !is s3);
	assert(tc.getCapacity(s4[0 .. 80]) == 80);

	// Decrease:
	auto s5 = tc.realloc(s4, 60, false);
	assert(s5 !is s4);
	assert(tc.getCapacity(s5[0 .. 64]) == 64);
}

unittest arraySpill {
	ThreadCache tc;
	tc.initialize(&gExtentMap, &gBase);

	void setAllocationUsedCapacity(void* ptr, size_t usedCapacity) {
		assert(ptr !is null);

		auto pd = tc.getPageDescriptor(ptr);
		assert(pd.extent !is null);

		if (pd.isSlab()) {
			auto si = SlabAllocInfo(pd, ptr);
			si.setUsedCapacity(usedCapacity);
		} else {
			pd.extent.setUsedCapacity(usedCapacity);
		}
	}

	// Get two allocs of given size guaranteed to be adjacent.
	void*[2] makeTwoAdjacentAllocs(uint size) {
		void* alloc() {
			return tc.alloc(size, false, false);
		}

		void*[2] tryPair(void* left, void* right) {
			assert(left !is null);
			assert(right !is null);

			if (left + size is right) {
				return [left, right];
			}

			auto pair = tryPair(right, alloc());
			tc.free(left);
			return pair;
		}

		return tryPair(alloc(), alloc());
	}

	void testSpill(uint arraySize, uint[] capacities) {
		auto pair = makeTwoAdjacentAllocs(arraySize);
		void* a0 = pair[0];
		void* a1 = pair[1];
		assert(a1 == a0 + arraySize);

		void testZeroLengthSlices() {
			foreach (a0Capacity; capacities) {
				setAllocationUsedCapacity(a0, a0Capacity);
				// For all possible zero-length slices of a0:
				foreach (s; 0 .. arraySize + 1) {
					// A zero-length slice has non-zero capacity if and only if it
					// resides at the start of the freespace of a non-empty alloc:
					auto sliceCapacity = tc.getCapacity(a0[s .. s]);
					auto haveCapacity = sliceCapacity > 0;
					assert(haveCapacity
						== (s == a0Capacity && s > 0 && s < arraySize));
					// Capacity in non-degenerate case follows standard rule:
					assert(!haveCapacity || sliceCapacity == arraySize - s);
				}
			}
		}

		// Try it with various capacities for a1:
		foreach (a1Capacity; capacities) {
			setAllocationUsedCapacity(a1, a1Capacity);
			testZeroLengthSlices();
		}

		// Same rules apply if the space above a0 is not allocated:
		tc.free(a1);
		testZeroLengthSlices();

		tc.free(a0);
	}

	testSpill(64, [0, 1, 2, 32, 63, 64]);
	testSpill(80, [0, 1, 2, 32, 79, 80]);
	testSpill(16384, [0, 1, 2, 500, 16000, 16383, 16384]);
	testSpill(20480, [0, 1, 2, 500, 20000, 20479, 20480]);
}

unittest finalization {
	ThreadCache tc;
	tc.initialize(&gExtentMap, &gBase);

	// Faux destructor which simply records most recent kill:
	static size_t lastKilledUsedCapacity = 0;
	static void* lastKilledAddress;
	static uint destroyCount = 0;
	static void destruct(void* ptr, size_t size) {
		lastKilledUsedCapacity = size;
		lastKilledAddress = ptr;
		destroyCount++;
	}

	// Finalizers for large allocs:
	auto s0 = tc.allocAppendable(16384, false, false, &destruct);
	tc.destroy(s0);
	assert(lastKilledAddress == s0);
	assert(lastKilledUsedCapacity == 16384);

	// Destroy on non-finalized alloc is harmless:
	auto s1 = tc.allocAppendable(20000, false, false);
	auto oldDestroyCount = destroyCount;
	tc.destroy(s1);
	assert(destroyCount == oldDestroyCount);

	// Finalizers for small allocs:
	auto s2 = tc.allocAppendable(45, false, false, &destruct);
	assert(tc.getCapacity(s2[0 .. 45]) == 56);
	assert(!tc.extend(s2[0 .. 45], 12));
	assert(tc.extend(s2[0 .. 45], 11));
	assert(tc.getCapacity(s2[0 .. 56]) == 56);
	tc.destroy(s2);
	assert(lastKilledAddress == s2);
	assert(lastKilledUsedCapacity == 56);

	// Behaviour of realloc() on small allocs with finalizers:
	auto s3 = tc.allocAppendable(70, false, false, &destruct);
	assert(tc.getCapacity(s3[0 .. 70]) == 72);
	auto s4 = tc.realloc(s3, 70, false);
	assert(s3 == s4);

	// This is in the same size class, but will not work in-place
	// given as finalizer occupies final 8 of the 80 bytes in the slot:
	auto s5 = tc.realloc(s4, 75, false);
	assert(s5 != s4);

	// So we end up with a new alloc, without metadata:
	assert(tc.getCapacity(s5[0 .. 80]) == 80);

	// And the finalizer has been discarded:
	oldDestroyCount = destroyCount;
	tc.destroy(s5);
	assert(destroyCount == oldDestroyCount);
}
