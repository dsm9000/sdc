module d.gc.extent;

import d.gc.base;
import d.gc.heap;
import d.gc.rbtree;
import d.gc.sizeclass;
import d.gc.util;

alias ExtentTree = RBTree!(Extent, addrRangeExtentCmp);

alias PHNode = heap.Node!Extent;
alias RBNode = rbtree.Node!Extent;

struct Extent {
	enum Align = MetadataSlotSize;

private:
	ulong bits;

public:
	import d.gc.arena;
	Arena* arena;

	void* addr;
	size_t size;

	import d.gc.hpd;
	HugePageDescriptor* hpd;

	// Not necesserly unique, as splitting an Extent
	// Will create two extent with the same serial.
	// size_t serialNumber;

private:
	union Links {
		PHNode phnode;
		RBNode rbnode;
	}

	Links _links;

	import d.gc.bitmap;
	Bitmap!512 _slabData;

public:
	this(Arena* arena, void* addr, size_t size, HugePageDescriptor* hpd,
	     bool is_slab, ubyte sizeClass) {
		// FIXME: in contract.
		assert(sizeClass < ClassCount.Small,
		       "Invalid size class for small extent!");

		this.arena = arena;
		this.addr = addr;
		this.size = size;
		this.hpd = hpd;

		import d.gc.bin;
		bits = is_slab;
		bits |= ulong(sizeClass) << 58;
		bits |= ulong(binInfos[sizeClass].slots) << 48;
	}

	this(Arena* arena, void* addr, size_t size, HugePageDescriptor* hpd) {
		// FIXME: Overload resolution doesn't cast this properly.
		this(arena, addr, size, hpd, false, ubyte(0));
	}

	this(Arena* arena, void* addr, size_t size, HugePageDescriptor* hpd,
	     ubyte sizeClass) {
		this(arena, addr, size, hpd, true, sizeClass);
	}

	@property
	ref PHNode phnode() {
		return _links.phnode;
	}

	@property
	ref RBNode rbnode() {
		return _links.rbnode;
	}

	bool contains(void* ptr) const {
		return ptr >= addr && ptr < addr + size;
	}

	/**
	 * Slab features.
	 */
	bool isSlab() const {
		return (bits & 0x01) != 0;
	}

	@property
	ubyte sizeClass() const {
		// FIXME: in contract.
		assert(isSlab(), "slabData accessed on non slab!");

		ubyte sc = bits >> 58;

		// FIXME: out contract.
		assert(sc < ClassCount.Small);
		return sc;
	}

	@property
	uint freeSlots() const {
		// FIXME: in contract.
		assert(isSlab(), "slabData accessed on non slab!");

		enum Mask = (1 << 10) - 1;
		return (bits >> 48) & Mask;
	}

	uint allocate() {
		// FIXME: in contract.
		assert(isSlab(), "slabData accessed on non slab!");
		assert(freeSlots > 0, "Slab is full!");

		scope(success) bits -= (1UL << 48);
		return slabData.setFirst();
	}

	void free(uint index) {
		// FIXME: in contract.
		assert(isSlab(), "slabData accessed on non slab!");
		assert(slabData.valueAt(index), "Slot is already free!");

		bits += (1UL << 48);
		slabData.clearBit(index);
	}

	@property
	ref Bitmap!512 slabData() {
		// FIXME: in contract.
		assert(isSlab(), "slabData accessed on non slab!");

		return _slabData;
	}
}

static assert(Extent.sizeof == Extent.Align, "Unexpected Extent size!");
static assert(Extent.sizeof == MetadataSlotSize, "Extent got too large!");

ptrdiff_t identityExtentCmp(Extent* lhs, Extent* rhs) {
	auto l = cast(size_t) lhs;
	auto r = cast(size_t) rhs;

	// We need to compare that way to avoid integer overflow.
	return (l > r) - (l < r);
}

ptrdiff_t addrExtentCmp(Extent* lhs, Extent* rhs) {
	auto l = cast(size_t) lhs.addr;
	auto r = cast(size_t) rhs.addr;

	// We need to compare that way to avoid integer overflow.
	return (l > r) - (l < r);
}

ptrdiff_t addrRangeExtentCmp(Extent* lhs, Extent* rhs) {
	auto l = cast(size_t) lhs.addr;
	auto rstart = cast(size_t) rhs.addr;
	auto rend = rstart + rhs.size;

	// We need to compare that way to avoid integer overflow.
	return (l >= rend) - (l < rstart);
}

unittest contains {
	auto base = cast(void*) 0x56789abcd000;
	enum Size = 1234;

	Extent e;
	e.addr = base;
	e.size = Size;

	assert(!e.contains(base - 1));
	assert(!e.contains(base + Size));

	foreach (i; 0 .. Size) {
		assert(e.contains(base + i));
	}
}

unittest allocfree {
	import d.gc.spec;
	auto e = Extent(null, null, PageSize, null, ubyte(0));

	assert(e.isSlab());
	assert(e.sizeClass == 0);
	assert(e.freeSlots == 512);

	assert(e.allocate() == 0);
	assert(e.freeSlots == 511);

	assert(e.allocate() == 1);
	assert(e.freeSlots == 510);

	assert(e.allocate() == 2);
	assert(e.freeSlots == 509);

	e.free(1);
	assert(e.freeSlots == 510);

	assert(e.allocate() == 1);
	assert(e.freeSlots == 509);

	assert(e.allocate() == 3);
	assert(e.freeSlots == 508);

	e.free(0);
	e.free(3);
	e.free(2);
	e.free(1);
	assert(e.freeSlots == 512);
}
