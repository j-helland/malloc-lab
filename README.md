# Implementation of `malloc` in C for CMU 15213

A 64-bit struct-based segmented free list memory allocator.
Provides `malloc`, `free`, `calloc`, and `realloc` implementations.

An experimental branch using splay-trees for managing certain memory blocks is also available.

### **WARNING**
This code will not compile as-is. It was written to interface with a larger test harness that includes memory emulation. In particular, the heap is simulated e.g. functions like `mem_sbrk` exist in place of standard `sbrk`.
Descriptions of these functions are provided in [`memlib.h`](./memlib.h), which should provide enough context to port this code to the canonical C UNIX functions if desired.

# Organization

### [`mm.c`](./mmc)
1. Constants, structs, globals, etc.

2. Helper functions. These operate on a specific subcomponent of the heap
   e.g. seglist_insert.
  a. Math & misc b. Get data: access metadata from a block.
  c. Set data: write metadata to a block.
  d. Basic search: find blocks matching various specifications.
  e. Freelist helpers: functions that interact exclusively with an
     individual freelist data structure.
  f. Seglist helpers: functions that interact with the entire segmented
     list data structure.

3. Primary heap routines. These operate on the entire heap in some way e.g.
   mm_malloc, mm_free.

4. Debugging functions. These include heap checker functions and printing
   functions that are handy in gdb e.g. print_heap.

### [`memlib.h`](./memlib.h)

A bare header that only exists to provide descriptions of the heap simulator functions so that this code can be ported over to use canonical C UNIX functions instead if so desired.

# Documentation
You'll find that most of the standard tricks for malloc performance have been
implemented here e.g. segregated freelists, small memory bins with footer-less blocks, 
free block coalescing, mixture of FIFO and LIFO policies depending on block sizes.

 This malloc implementation organizes blocks according to their sizes via a
 segregated list. The segregated list itself contains bins corresponding to
 "small" blocks and "large" blocks. Blocks within a small bin all have the
 same size and are strung together by a singly-linked list -- this
 means that minimal overhead is required. Large bins contain blocks of varying
 sizes within some pre-determined range and are thus connected together via a
 doubly-linked, circular list. By reserving this overhead only for larger
 blocks, we minimize wasted space since a sufficiently large block will
 already have enough capacity in its payload for the next/prev list pointers.

 Pictorially, the segregated list has the following bin structure:
 ```
  ---- ---- ----       ---- -----       -------
 | 16 | 32 | 40 | ... | 64 | 128 | ... | 16384 |
  ---- ---- ----       ---- -----       -------
 small <-----------------large---------------->
 ```

 Even though only the first bin is marked as "small", the size 32 bin is de
 facto small as well due to the 16-byte address alignment requirement. We
 could actually do much better in terms of utilization if we removed the
 alignment constraint for small bins - there are many 24 byte allocations, for
 example. However, the alignment requirement of this assignment means that it
 only makes sense to have a single small bin.

 Starting at bin size 32, we increase in size by increments of 8 up to size
 64, at which point we begin doubling the bin size at each step. This is
 because of the roughly power-law distributed allocation sizes that we see in
 practice across all traces. We want to have a fairly fine level of
 granularity for small bins, whereas larger allocation sizes will occur
 relatively rarely.

 Within the small bin, the blocks follow a typical singly-linked list
 structure. Each node has one size.
 Our insertion policy here is at the head i.e. O(1). Removal can happen
 anywhere i.e. O(n).
 ```
  ----      ----             ----
 | 16 | -> | 16 | -> ... -> | 16 | -> NULL
  ----      ----             ----
```

 The large bins are doubly linked and circular. Each node has a varying size.
 The circularity is an implementation convenience - it allows for fewer
 global variables if we want to do things like tail insertion.
 Our insertion policy is slightly more complicated here:
 - If a block is small enough, we insert at the head.
 - If a block is large enough, we insert at the tail.
 Experimentally, I found that head insertion for the 32-64 sized bins and
 tail insertion for the 128-16384 sized bins performs pretty well in terms of
 throughput while not sacrificing too much utilization.
 ```
           ----       ----               ----
 tail <-> |    | <-> |    | <-> ... <-> |    | <-> head
           ----       ----               ----
           head                          tail
```

 To find a block fit when calling malloc, I use a first-fit policy. Starting
 at the smallest bin size with sufficient capacity for the request, the
 search traverses through the freelist starting at the head, moving up to
 the next bin if no match is found.

 Upon finding a match, we split the block down to the requested size (plus
 overhead), adding the split off block back into the seglist.

 O(1) coalescing is implemented with an immediate-coalesce policy, meaning
 that we coalesce immediately upon a free operation.


### **OPTIMIZATIONS**
 Here I describe in a bulleted fashion the most significant performance
 improvements. Much of this information is contained in the above
 overview of the system.

 - Segmented list of freelists. This approximates a best fit policy well
   enough that we can get away with a fast first-fit policy for finding
   free blocks. This improves both utilization and throughput.

 - No footers for small blocks, instead we use a bit in the header that
   indicates the allocations status of the previous block. This improves
   utilization.

 - Singly linked list for small blocks i.e. only the header and one
   next pointer. This improves utilization.

 - A mixture of LIFO and FIFO insertion policies in large bins depending
   on the size of the bin. This increases throughput with a negligible
   decrease in utilization.

### **FUTURE IMPROVEMENTS**
 - In theory, a search tree would help with utilization for bins that
   have high entropy in their distribution of block sizes. This tends
   to be the case for the largest bins (recall that the allocation
   sizes tend to follow a power-law distribution and the large bins
   exist in the tail regime of this distribution). This would allow
   an efficient best-fit policy for these bins.

### **FAILED EXPERIMENTS**
 - Splay trees to order blocks by size did not seem to help. In fact,
   utilization did not seem to improve while throughput significantly
   decreased. I suspect this was due to the overhead of the splay
   operation after every insertion and deletion.
   Note: I used a best-fit policy for the splay tree.