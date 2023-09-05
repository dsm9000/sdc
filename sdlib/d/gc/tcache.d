module d.gc.tcache;

import d.gc.sizeclass;
import d.gc.spec;
import d.gc.util;

ThreadCache threadCache;

struct ThreadCache {
private:
	import d.gc.emap;
	shared(ExtentMap)* emap;

	const(void)* stackBottom;
	const(void*)[][] roots;

	// Data returned in response to capacity queries.
	struct CapacityInfo {
		void* address;
		size_t size;
		size_t usedCapacity;

		this(void* address, size_t size, size_t used) {
			assert(used <= size, "Used capacity exceeds alloc size!");

			this.address = address;
			this.size = size;
			this.usedCapacity = used;

			import core.stdc.stdio;
			printf("size = %d, usedCapacity = %d\n", size, usedCapacity);
		}
	}

public:
	void* alloc(size_t size, bool containsPointers) {
		if (!isAllocatableSize(size)) {
			return null;
		}

		initializeExtentMap();

		auto arena = chooseArena(containsPointers);
		return isSmallSize(size)
			? arena.allocSmall(emap, size)
			: arena.allocLarge(emap, size, false);
	}

	void* allocAppendable(size_t size, bool containsPointers) {
		auto asize = alignUp(size, 2 * Quantum);
		assert(isAppendableSizeClass(getSizeClass(asize)),
		       "allocAppendable got non-appendable size class!");
		auto ptr = alloc(asize, containsPointers);
		// Remember the size we actually use.
		auto pd = getPageDescriptor(ptr);
		setUsedCapacity(pd, ptr, size);
		return ptr;
	}

	void* calloc(size_t size, bool containsPointers) {
		if (!isAllocatableSize(size)) {
			return null;
		}

		initializeExtentMap();

		auto arena = chooseArena(containsPointers);
		if (isLargeSize(size)) {
			return arena.allocLarge(emap, size, true);
		}

		auto ret = arena.allocSmall(emap, size);
		memset(ret, 0, size);
		return ret;
	}

	void free(void* ptr) {
		if (ptr is null) {
			return;
		}

		auto pd = getPageDescriptor(ptr);
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
			return alloc(size, containsPointers);
		}

		auto pd = getPageDescriptor(ptr);
		auto info = getAllocInfo(pd, ptr);
		auto copySize = min(size, info.usedCapacity);
		auto samePointerness = containsPointers == pd.containsPointers;

		if (pd.isSlab()) {
			auto newSizeClass = getSizeClass(size);
			auto oldSizeClass = pd.sizeClass;
			if (samePointerness && newSizeClass == oldSizeClass) {
				setUsedCapacity(pd, ptr, size);
				return ptr;
			}
		} else {
			auto esize = pd.extent.size;
			if (samePointerness && alignUp(size, PageSize) == esize) {
				pd.extent.setUsedCapacity(size);
				return ptr;
			}
		}

		auto newPtr = alloc(size, containsPointers);
		if (newPtr is null) {
			return null;
		}

		auto npd = getPageDescriptor(newPtr);
		setUsedCapacity(npd, newPtr, size);

		import core.stdc.stdio;
		printf("set used = %d\n", size);
		
		memcpy(newPtr, ptr, copySize);
		pd.arena.free(emap, pd, ptr);

		return newPtr;
	}

	/**
	 * Appendable facilities.
	 */

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
	bool getAppendablePageDescriptor(const void[] slice, ref PageDescriptor pd,
	                                 ref CapacityInfo info) {
		pd = maybeGetPageDescriptor(slice.ptr);
		if (pd.extent is null) {
			return false;
		}

		info = getAllocInfo(pd, cast(void*) slice.ptr);

		// Slice must not end before valid data ends, or capacity is zero:
		auto startIndex = slice.ptr - info.address;
		auto stopIndex = startIndex + slice.length;

		// If the slice end doesn't match the used capacity, not appendable.
		return stopIndex == info.usedCapacity;
	}

	size_t getCapacity(const void[] slice) {
		PageDescriptor pd;
		CapacityInfo info;
		if (!getAppendablePageDescriptor(slice, pd, info)) {
			return 0;
		}

		auto startIndex = slice.ptr - info.address;
		return info.size - startIndex;
	}

	bool extend(const void[] slice, size_t size) {
		if (size == 0) {
			return true;
		}

		PageDescriptor pd;
		CapacityInfo info;
		if (!getAppendablePageDescriptor(slice, pd, info)) {
			return false;
		}

		// There must be sufficient free space to extend into:
		auto newCapacity = info.usedCapacity + size;
		if (info.size < newCapacity) {
			return false;
		}

		// Increase the used capacity by the requested size:
		return setUsedCapacity(pd, info.address, newCapacity);
	}

	/**
	 * GC facilities.
	 */
	void addRoots(const void[] range) {
		auto ptr = cast(void*) roots.ptr;

		// We realloc everytime. It doesn't really matter at this point.
		roots.ptr = cast(const(void*)[]*)
			realloc(ptr, (roots.length + 1) * void*[].sizeof, true);

		// Using .ptr to bypass bound checking.
		roots.ptr[roots.length] = makeRange(range);

		// Update the range.
		roots = roots.ptr[0 .. roots.length + 1];
	}

	void collect() {
		// TODO: The set need a range interface or some other way to iterrate.
		// FIXME: Prepare the GC so it has bitfields for all extent classes.

		// Scan the roots !
		__sd_gc_push_registers(scanStack);
		foreach (range; roots) {
			scan(range);
		}

		// TODO: Go on and on until all worklists are empty.

		// TODO: Collect.
	}

	bool scanStack() {
		import sdc.intrinsics;
		auto framePointer = readFramePointer();
		auto length = stackBottom - framePointer;

		auto range = makeRange(framePointer[0 .. length]);
		return scan(range);
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
				// We have no mappign there.
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
	CapacityInfo getAllocInfo(PageDescriptor pd, void* ptr) {
		if (pd.extent.isLarge()) {
			return CapacityInfo(pd.extent.address, pd.extent.size,
			                    pd.extent.usedCapacity);
		}

		// Slab alloc:
		import d.gc.bin;
		auto sg = slabAllocGeometry(ptr, pd, false);

		// If freespace flag is 0, or this size class does not support meta,
		// then the alloc is reported to be fully used:
		if (!sg.e.hasFreeSpace(sg.index)) {
			return CapacityInfo(sg.address, sg.size, sg.size);
		}

		// Decode freesize, found in the final byte (or two bytes) of the alloc:
		auto freeSize = readPackedU15(sg.address + sg.size - 2);

		return CapacityInfo(sg.address, sg.size, sg.size - freeSize);
	}

	bool setUsedCapacity(PageDescriptor pd, void* ptr, size_t usedCapacity) {
		if (pd.extent.isLarge()) {
			pd.extent.setUsedCapacity(usedCapacity);
			return true;
		}

		// Slab alloc:
		import d.gc.bin;
		auto sg = slabAllocGeometry(ptr, pd, true);

		assert(usedCapacity <= sg.size,
		       "Used capacity may not exceed alloc size!");

		// If this size class is not appendable, then let the caller know
		// that the used capacity did not change, as it is permanently fixed:
		if (!sg.e.allowsFreeSpace) {
			return false;
		}

		// If capacity of alloc is now fully used:
		if (usedCapacity == sg.size) {
			sg.e.clearFreeSpace(sg.index);
			return true;
		}

		// Encode freesize and write it to the last byte (or two bytes) of alloc.
		// Only 14 bits are required to cover all small size classes :
		ushort freeSize = 0x3fff & (sg.size - usedCapacity);
		writePackedU15(sg.address + sg.size - 2, freeSize);

		sg.e.setFreeSpace(sg.index);
		return true;
	}

	auto getPageDescriptor(void* ptr) {
		auto pd = maybeGetPageDescriptor(ptr);
		assert(pd.extent !is null);
		assert(pd.isSlab() || ptr is pd.extent.address);

		return pd;
	}

	auto maybeGetPageDescriptor(const void* ptr) {
		initializeExtentMap();

		import d.gc.util;
		auto aptr = alignDown(ptr, PageSize);
		return emap.lookup(aptr);
	}

	void initializeExtentMap() {
		import sdc.intrinsics;
		if (unlikely(emap is null)) {
			emap = gExtentMap;
		}
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

extern(C):
version(OSX) {
	// For some reason OSX's symbol get a _ prepended.
	bool _sd_gc_push_registers(bool delegate());
	alias __sd_gc_push_registers = _sd_gc_push_registers;
} else {
	bool __sd_gc_push_registers(bool delegate());
}

/**
 * This function get a void[] range and chnage it into a
 * const(void*)[] one, reducing to alignement boundaries.
 */
const(void*)[] makeRange(const void[] range) {
	auto begin = alignUp(range.ptr, PointerSize);
	auto end = alignDown(range.ptr + range.length, PointerSize);

	auto ibegin = cast(size_t) begin;
	auto iend = cast(size_t) end;
	if (ibegin > iend) {
		return [];
	}

	auto ptr = cast(void**) begin;
	auto length = (iend - ibegin) / PointerSize;

	return ptr[0 .. length];
}

unittest makeRange {
	static checkRange(const void[] range, size_t start, size_t stop) {
		auto r = makeRange(range);
		assert(r.ptr is cast(const void**) start);
		assert(r.ptr + r.length is cast(const void**) stop);
	}

	void* ptr;
	void[] range = ptr[0 .. 5];

	checkRange(ptr[0 .. 0], 0, 0);
	checkRange(ptr[0 .. 1], 0, 0);
	checkRange(ptr[0 .. 2], 0, 0);
	checkRange(ptr[0 .. 3], 0, 0);
	checkRange(ptr[0 .. 4], 0, 0);
	checkRange(ptr[0 .. 5], 0, 0);
	checkRange(ptr[0 .. 6], 0, 0);
	checkRange(ptr[0 .. 7], 0, 0);
	checkRange(ptr[0 .. 8], 0, 8);

	checkRange(ptr[1 .. 1], 0, 0);
	checkRange(ptr[1 .. 2], 0, 0);
	checkRange(ptr[1 .. 3], 0, 0);
	checkRange(ptr[1 .. 4], 0, 0);
	checkRange(ptr[1 .. 5], 0, 0);
	checkRange(ptr[1 .. 6], 0, 0);
	checkRange(ptr[1 .. 7], 0, 0);
	checkRange(ptr[1 .. 8], 8, 8);
}

unittest getCapacity {
	// Capacity of a non-appendable is zero:
	auto nonAppendable = threadCache.alloc(3, false);
	assert(threadCache.getCapacity(nonAppendable[0 .. 3]) == 0);

	// Capacity of any slice in space unknown to the GC is zero:
	void* nullPtr = null;
	assert(threadCache.getCapacity(nullPtr[0 .. 100]) == 0);

	void* stackPtr = &nullPtr;
	assert(threadCache.getCapacity(stackPtr[0 .. 100]) == 0);

	void* tlPtr = &threadCache;
	assert(threadCache.getCapacity(tlPtr[0 .. 100]) == 0);

	// Check capacity for a small appendable GC allocation.
	auto s0 = threadCache.allocAppendable(5, false);
	assert(threadCache.getCapacity(s0[0 .. 0]) == 0);
	assert(threadCache.getCapacity(s0[0 .. 5]) == 16);
	assert(threadCache.getCapacity(s0[1 .. 5]) == 15);
	assert(threadCache.getCapacity(s0[4 .. 5]) == 12);
	assert(threadCache.getCapacity(s0[5 .. 5]) == 11);

	// Out of range:
	assert(threadCache.getCapacity(s0[6 .. 6]) == 0);
	assert(threadCache.getCapacity(s0[99 .. 99]) == 0);

	// Realloc, capacity is set to target size:
	auto s1 = threadCache.realloc(s0, 100, false);
	assert(s1 !is s0);
	assert(threadCache.getCapacity(s1[0 .. 100]) == 112);

	// To larger, but still small, size class:
	auto s2 = threadCache.realloc(s1, 900, false);
	assert(s2 !is s1);
	assert(threadCache.getCapacity(s2[0 .. 900]) == 1024);

	// Realloc within the same small size class:
	auto s3 = threadCache.realloc(s2, 1000, false);
	assert(s3 is s2);
	assert(threadCache.getCapacity(s3[0 .. 1000]) == 1024);

	// Realloc to a large size class:
	auto s4 = threadCache.realloc(s3, 20000, false);
	assert(threadCache.getCapacity(s4[0 .. 20000]) == 20480);

	// Realloc to another small size class:
	auto s5 = threadCache.realloc(s4, 1500, false);
	assert(threadCache.getCapacity(s5[0 .. 1500]) == 1536);

	// Realloc down to a size class without appendability support:
	auto s6 = threadCache.realloc(s5, 24, false);
	assert(threadCache.getCapacity(s6[0 .. 5]) == 0);
	assert(threadCache.getCapacity(s6[0 .. 24]) == 24);

	// Check capacity for a large appendable GC allocation.
	auto p0 = threadCache.allocAppendable(16384, false);
	p0 = threadCache.realloc(p0, 16384, false);

	// Capacity of segment from p0, length 100 is 16384:
	assert(threadCache.getCapacity(p0[0 .. 16384]) == 16384);
	assert(threadCache.getCapacity(p0[1 .. 16384]) == 16383);
	assert(threadCache.getCapacity(p0[50 .. 16384]) == 16334);
	assert(threadCache.getCapacity(p0[99 .. 16384]) == 16285);
	assert(threadCache.getCapacity(p0[100 .. 16384]) == 16284);
	
	// If the slice doesn't go the end of the allocated area
	// then the capacity must be 0.
	assert(threadCache.getCapacity(p0[0 .. 0]) == 0);
	assert(threadCache.getCapacity(p0[0 .. 16383]) == 0);

	// This would almost certainly be a bug in userland,
	// but let's make sure be behave reasonably there.
	assert(threadCache.getCapacity(p0[0 .. 16385]) == 0);
	assert(threadCache.getCapacity(p0[1 .. 16385]) == 0);
	assert(threadCache.getCapacity(p0[50 .. 16385]) == 0);
	assert(threadCache.getCapacity(p0[100 .. 16385]) == 0);
	assert(threadCache.getCapacity(p0[101 .. 16385]) == 0);

	// Realloc.
	auto p1 = threadCache.allocAppendable(20000, false);
	assert(threadCache.getCapacity(p1[0 .. 19999]) == 0);
	assert(threadCache.getCapacity(p1[0 .. 20000]) == 20480);
	assert(threadCache.getCapacity(p1[0 .. 20001]) == 0);

	// Decreasing the size of the allocation
	// should adjust capacity acordingly.
	auto p2 = threadCache.realloc(p1, 19999, false);
	assert(p2 is p1);

	assert(threadCache.getCapacity(p2[0 .. 19999]) == 20480);
	assert(threadCache.getCapacity(p2[0 .. 20000]) == 0);
	assert(threadCache.getCapacity(p2[0 .. 20001]) == 0);

	// Increasing the size of the allocation increases capacity.
	auto p3 = threadCache.realloc(p2, 20001, false);
	assert(p3 is p2);

	assert(threadCache.getCapacity(p3[0 .. 19999]) == 0);
	assert(threadCache.getCapacity(p3[0 .. 20000]) == 0);
	assert(threadCache.getCapacity(p3[0 .. 20001]) == 20480);

	auto p4 = threadCache.realloc(p3, 16000, false);
	assert(p4 !is p3);
	assert(threadCache.getCapacity(p4[0 .. 16000]) == 16384);

	auto p5 = threadCache.realloc(p4, 20000, false);
	assert(p5 !is p4);
	assert(threadCache.getCapacity(p5[0 .. 20000]) == 20480);
}

unittest extend {
	auto nonAppendable = threadCache.alloc(100, false);

	// Attempt to extend a non-appendable:
	assert(!threadCache.extend(nonAppendable[0 .. 100], 1));

	// Extend by zero is permitted even when no capacity:
	assert(threadCache.extend(nonAppendable[0 .. 100], 0));

	// Extend in space unknown to the GC. Can only extend by zero.
	void* nullPtr = null;
	assert(threadCache.extend(nullPtr[0 .. 100], 0));
	assert(!threadCache.extend(nullPtr[0 .. 100], 1));
	assert(!threadCache.extend(nullPtr[100 .. 100], 1));

	void* stackPtr = &nullPtr;
	assert(threadCache.extend(stackPtr[0 .. 100], 0));
	assert(!threadCache.extend(stackPtr[0 .. 100], 1));
	assert(!threadCache.extend(stackPtr[100 .. 100], 1));

	void* tlPtr = &threadCache;
	assert(threadCache.extend(tlPtr[0 .. 100], 0));
	assert(!threadCache.extend(tlPtr[0 .. 100], 1));
	assert(!threadCache.extend(tlPtr[100 .. 100], 1));

	// Make an appendable alloc:
	auto p0 = threadCache.allocAppendable(100, false);
	assert(threadCache.getCapacity(p0[0 .. 100]) == 16384);

	// Attempt to extend valid slices with capacity 0.
	// (See getCapacity tests.)
	assert(threadCache.extend(p0[0 .. 0], 0));
	assert(!threadCache.extend(p0[0 .. 0], 50));
	assert(!threadCache.extend(p0[0 .. 99], 50));
	assert(!threadCache.extend(p0[1 .. 99], 50));
	assert(!threadCache.extend(p0[0 .. 50], 50));

	// Extend by size zero is permitted but has no effect:
	assert(threadCache.extend(p0[100 .. 100], 0));
	assert(threadCache.extend(p0[0 .. 100], 0));
	assert(threadCache.getCapacity(p0[0 .. 100]) == 16384);
	assert(threadCache.extend(p0[50 .. 100], 0));
	assert(threadCache.getCapacity(p0[50 .. 100]) == 16334);

	// Attempt extend with insufficient space (one byte too many) :
	assert(threadCache.getCapacity(p0[100 .. 100]) == 16284);
	assert(!threadCache.extend(p0[0 .. 100], 16285));
	assert(!threadCache.extend(p0[50 .. 100], 16285));

	// Extending to the limit (one less than above) succeeds:
	assert(threadCache.extend(p0[50 .. 100], 16284));

	// Now we're full, and can extend only by zero:
	assert(threadCache.extend(p0[0 .. 16384], 0));
	assert(!threadCache.extend(p0[0 .. 16384], 1));

	// Make another appendable alloc:
	auto p1 = threadCache.allocAppendable(100, false);
	assert(threadCache.getCapacity(p1[0 .. 100]) == 16384);

	// Valid extend :
	assert(threadCache.extend(p1[0 .. 100], 50));
	assert(threadCache.getCapacity(p1[100 .. 150]) == 16284);
	assert(threadCache.extend(p1[0 .. 150], 0));

	// Capacity of old slice becomes 0:
	assert(threadCache.getCapacity(p1[0 .. 100]) == 0);

	// The only permitted extend is by 0:
	assert(threadCache.extend(p1[0 .. 100], 0));

	// Capacity of a slice including the original and the extension:
	assert(threadCache.getCapacity(p1[0 .. 150]) == 16384);

	// Extend the upper half:
	assert(threadCache.extend(p1[125 .. 150], 100));
	assert(threadCache.getCapacity(p1[150 .. 250]) == 16234);

	// Original's capacity becomes 0:
	assert(threadCache.getCapacity(p1[125 .. 150]) == 0);
	assert(threadCache.extend(p1[125 .. 150], 0));

	// Capacity of a slice including original and extended:
	assert(threadCache.extend(p1[125 .. 250], 0));
	assert(threadCache.getCapacity(p1[125 .. 250]) == 16259);

	// Capacity of earlier slice elongated to cover the extensions :
	assert(threadCache.getCapacity(p1[0 .. 250]) == 16384);

	// Extend a zero-size slice existing at the start of the free space:
	assert(threadCache.extend(p1[250 .. 250], 200));
	assert(threadCache.getCapacity(p1[250 .. 450]) == 16134);

	// Capacity of the old slice is now 0:
	assert(threadCache.getCapacity(p1[0 .. 250]) == 0);

	// Capacity of a slice which includes the original and the extension:
	assert(threadCache.getCapacity(p1[0 .. 450]) == 16384);

	// Extend so as to fill up all but one byte of free space:
	assert(threadCache.extend(p1[0 .. 450], 15933));
	assert(threadCache.getCapacity(p1[16383 .. 16383]) == 1);

	// Extend, filling up last byte of free space:
	assert(threadCache.extend(p1[16383 .. 16383], 1));
	assert(threadCache.getCapacity(p1[0 .. 16384]) == 16384);

	// Attempt to extend, but we're full:
	assert(!threadCache.extend(p1[0 .. 16384], 1));

	// Extend by size zero still works, though:
	assert(threadCache.extend(p1[0 .. 16384], 0));
}

unittest extend {
	// Attempt to extend a non-appendable:
	auto nonAppendable = threadCache.alloc(1, false);
	assert(!threadCache.extend(nonAppendable[0 .. 1], 1));

	// Extend by zero is permitted at all times:
	assert(threadCache.extend(nonAppendable[0 .. 100], 0));

	void* nullPtr = null;
	assert(threadCache.extend(nullPtr[0 .. 100], 0));

	void* stackPtr = &nullPtr;
	assert(threadCache.extend(stackPtr[0 .. 100], 0));

	void* tlPtr = &threadCache;
	assert(threadCache.extend(tlPtr[0 .. 100], 0));

	// Make a small appendable alloc:
	auto s0 = threadCache.allocAppendable(42, false);

	assert(threadCache.getCapacity(s0[0 .. 42]) == 48);
	assert(threadCache.extend(s0[0 .. 0], 0));
	assert(!threadCache.extend(s0[0 .. 0], 10));
	assert(!threadCache.extend(s0[0 .. 41], 10));
	assert(!threadCache.extend(s0[1 .. 41], 10));
	assert(!threadCache.extend(s0[0 .. 20], 10));

	// Attempt extend with insufficient space:
	assert(!threadCache.extend(s0[0 .. 42], 23));
	assert(!threadCache.extend(s0[32 .. 42], 23));

	// Valid extend :
	assert(threadCache.extend(s0[0 .. 42], 3));

	// Capacity of old slice becomes 0:
	assert(threadCache.getCapacity(s0[0 .. 42]) == 0);

	// Capacity of extended slice:
	assert(threadCache.getCapacity(s0[0 .. 45]) == 48);

	// Extend again:
	assert(threadCache.extend(s0[40 .. 45], 2));
	assert(threadCache.getCapacity(s0[0 .. 45]) == 0);
	assert(threadCache.getCapacity(s0[0 .. 47]) == 48);

	// Resize to another small size class and extend :
	auto s1 = threadCache.realloc(s0, 440, false);
	assert(threadCache.extend(s1[0 .. 47], 5));
	assert(threadCache.getCapacity(s1[0 .. 47]) == 0);
	assert(threadCache.getCapacity(s1[0 .. 52]) == 448);

	// Resize and extend again:
	auto s2 = threadCache.realloc(s1, 220, false);
	assert(threadCache.extend(s2[0 .. 52], 100));
	assert(threadCache.getCapacity(s2[0 .. 152]) == 224);

	// Fill it up:
	assert(threadCache.extend(s2[0 .. 152], 59));
	assert(threadCache.getCapacity(s2[0 .. 211]) == 224);

	// Resize to a large size class and extend again:
	auto s3 = threadCache.realloc(s2, 20000, false);
	assert(threadCache.extend(s3[0 .. 211], 10000));
	assert(threadCache.getCapacity(s3[0 .. 10211]) == 20480);

	// Resize down to small size class, truncating:
	auto s4 = threadCache.realloc(s3, 80, false);
	assert(threadCache.getCapacity(s4[0 .. 10211]) == 0);
	assert(threadCache.getCapacity(s4[0 .. 80]) == 80);

	// Make a large appendable alloc:
	auto p0 = threadCache.allocAppendable(100, false);
	p0 = threadCache.realloc(p0, 16384, false);
	assert(threadCache.getCapacity(p0[0 .. 100]) == 16384);

	// Attempt to extend slices with capacity 0:
	assert(threadCache.extend(p0[0 .. 0], 0));
	assert(!threadCache.extend(p0[0 .. 0], 50));
	assert(!threadCache.extend(p0[0 .. 99], 50));
	assert(!threadCache.extend(p0[1 .. 99], 50));
	assert(!threadCache.extend(p0[0 .. 50], 50));

	// Attempt extend with insufficient space:
	assert(!threadCache.extend(p0[0 .. 100], 16285));
	assert(!threadCache.extend(p0[50 .. 100], 16285));

	// Extend by size zero is permitted but has no effect:
	assert(threadCache.extend(p0[100 .. 100], 0));
	assert(threadCache.extend(p0[0 .. 100], 0));
	assert(threadCache.getCapacity(p0[0 .. 100]) == 16384);
	assert(threadCache.extend(p0[50 .. 100], 0));
	assert(threadCache.getCapacity(p0[50 .. 100]) == 16334);

	// Valid extend :
	assert(threadCache.extend(p0[0 .. 100], 50));
	assert(threadCache.getCapacity(p0[100 .. 150]) == 16284);

	// Capacity of old slice becomes 0:
	assert(threadCache.getCapacity(p0[0 .. 100]) == 0);

	// The only permitted extend is by 0:
	assert(threadCache.extend(p0[0 .. 100], 0));

	// Capacity of a slice including the original and the extension:
	assert(threadCache.getCapacity(p0[0 .. 150]) == 16384);

	// Extend the upper half:
	assert(threadCache.extend(p0[125 .. 150], 100));
	assert(threadCache.getCapacity(p0[150 .. 250]) == 16234);

	// Original's capacity becomes 0:
	assert(threadCache.getCapacity(p0[125 .. 150]) == 0);

	// Capacity of a slice including original and extended:
	assert(threadCache.getCapacity(p0[125 .. 250]) == 16259);

	// Capacity of earlier slice elongated to cover the extensions :
	assert(threadCache.getCapacity(p0[0 .. 250]) == 16384);

	// Extend a zero-size slice existing at the start of the free space:
	assert(threadCache.extend(p0[250 .. 250], 200));
	assert(threadCache.getCapacity(p0[250 .. 450]) == 16134);

	// Capacity of the old slice is now 0:
	assert(threadCache.getCapacity(p0[0 .. 250]) == 0);

	// Capacity of a slice which includes the original and the extension:
	assert(threadCache.getCapacity(p0[0 .. 450]) == 16384);

	// Extend so as to fill up all but one byte of free space:
	assert(threadCache.extend(p0[0 .. 450], 15933));
	assert(threadCache.getCapacity(p0[16383 .. 16383]) == 1);

	// Extend, filling up last byte of free space:
	assert(threadCache.extend(p0[16383 .. 16383], 1));
	assert(threadCache.getCapacity(p0[0 .. 16384]) == 16384);

	// Attempt to extend, but we're full:
	assert(!threadCache.extend(p0[0 .. 16384], 1));

	// Extend by size zero still works, though:
	assert(threadCache.extend(p0[0 .. 16384], 0));
}
