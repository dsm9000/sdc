//T compiles:yes
//T has-passed:yes
//T retval:0
// msize test.

extern(C) void __sd_gc_free(void* ptr);
extern(C) size_t __sd_gc_msize(void* ptr);

int main() {
	// only small allocs currently
	foreach (size; 0 .. 4096) {
		auto mem = __sd_gc_alloc(size);
		auto msize = __sd_gc_msize(mem);
		assert(size == msize);
		__sd_gc_free(mem);
	}

	return 0;
}
