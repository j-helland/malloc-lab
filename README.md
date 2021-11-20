# Implementation of `malloc` in C for CMU 15213

This branch provides an experimental splay tree implementation to manage larger block sizes.
I unfortunately didn't have time to fully explore tree-based free block managers to my satisfaction.

### **Why search trees?**
The idea for using BSTs to manage free blocks is that best-fit allocation policies can be significantly sped-up to O(log n) time instead of O(n) time with the standard freelist.
If we restrict ourslves to only using BSTs for sufficiently large free blocks, we can be clever and cram all of the memory overhead required for the data structure into the memory blocks themselves.
With the right coalescing policy and usage patterns, we can expect lots of relatively large free blocks and thus the O(log n) search time becomes important.

A best-fit policy is desirable because it reduces the external fragmentation introduced by splitting blocks that are too large -- this means that we can theoretically get better memory utilization.

This could probably be further optimized with the right tree balancing (e.g. min heap).

### **Why splay trees?**
Splay trees are a really cool data structure that adaptively specializes itself towards its usage patterns.
In this sense, one might even consider a splay tree to be a primitive form of active learning.

A splay tree implements a certain balancing policy based on repeated access.
In particular, the idea of the splay tree is to re-balance the tree so that the most frequent accesses become the fastest.
Practically, this means that if we use a splay-tree to manage free blocks, then repeated allocations of the same size will get faster and faster even though we use a best-fit policy.

In other words, if we know that usage patterns for our dynamic allocator request many similarly sized blocks in a row, then we can optimize for this situation using splay trees.
Unfortunately, the traces used by the test harness include many other usage patterns that do not fit this use-case very well, so I did not find an overall performance boost with this current implementation.

### **Possible improvements**
- I my implementation keeps the same segregated list bin ranges that worked well for the freelists and uses splay trees to manage the largest segments. 
    It might work better to increase the bin ranges for the splay tree managed segments so that each tree manages a larger range of block sizes.
    That way, the splaying operation over time will roughly approximate the more fine-grained binning scheme.
- Deciding when to splay the tree needs further consideration. 
    In my current implementation, the tree splays both on insertion and deletion, meaning that splays happen on malloc and free calls.
    Prioritizing splays on allocations might help.
- Deciding when we actually need the best-fit policy needs more thought. 
    Can we monitor external fragmentation and adapt our fitting policy accordingly? 
    This should help with only using the algorithmic overhead of the splay tree when we actually need it.