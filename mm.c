/**
 * @author Jonathan Helland
 * @file mm.c
 * @brief A 64-bit struct-based segmented free list memory allocator.
 *
 * 15-213: Introduction to Computer Systems
 *
 **************** ORGANIZATION
 * The code is organized into the follow sections:
 *
 * 1. Constants, structs, globals, etc.
 *
 * 2. Helper functions. These operate on a specific subcomponent of the heap
 *    e.g. seglist_insert.
 *   a. Math & misc b. Get data: access metadata from a block.
 *   c. Set data: write metadata to a block.
 *   d. Basic search: find blocks matching various specifications.
 *   e. Freelist helpers: functions that interact exclusively with an
 *      individual freelist data structure.
 *   f. Seglist helpers: functions that interact with the entire segmented
 *      list data structure.
 *
 * 3. Primary heap routines. These operate on the entire heap in some way e.g.
 *    mm_malloc, mm_free.
 *
 * 4. Debugging functions. These include heap checker functions and printing
 *    functions that are handy in gdb e.g. print_heap.
 *
 **************** DOCUMENTATION
 * OVERVIEW
 * This malloc implementation organizes blocks according to their sizes via a
 * segregated list. The segregated list itself contains bins corresponding to
 * "small" blocks and "large" blocks. Blocks within a small bin all have the
 * same size and are strung together by a singly-linked, list - this
 * means that minimal overhead is required. Large bins contain blocks of varying
 * sizes within some pre-determined range and are thus connected together via a
 * doubly-linked, circular list. By reserving this overhead only for larger
 * blocks, we minimize wasted space since a sufficiently large block will
 * already have enough capacity in its payload for the next/prev list pointers.
 *
 * Pictorially, the segregated list has the following bin structure:
 *  ---- ---- ----       ---- -----       -------
 * | 16 | 32 | 40 | ... | 64 | 128 | ... | 16384 |
 *  ---- ---- ----       ---- -----       -------
 * small <-----------------large---------------->
 *
 * Even though only the first bin is marked as "small", the size 32 bin is de
 * facto small as well due to the 16-byte address alignment requirement. We
 * could actually do much better in terms of utilization if we removed the
 * alignment constraint for small bins - there are many 24 byte allocations, for
 * example. However, the alignment requirement of this assignment means that it
 * only makes sense to have a single small bin.
 *
 * Starting at bin size 32, we increase in size by increments of 8 up to size
 * 64, at which point we begin doubling the bin size at each step. This is
 * because of the roughly power-law distributed allocation sizes that we see in
 * practice across all traces. We want to have a fairly fine level of
 * granularity for small bins, whereas larger allocation sizes will occur
 * relatively rarely.
 *
 * Within the small bin, the blocks follow a typical singly-linked list
 * structure. Each node has one size.
 * Our insertion policy here is at the head i.e. O(1). Removal can happen
 * anywhere i.e. O(n).
 *  ----      ----             ----
 * | 16 | -> | 16 | -> ... -> | 16 | -> NULL
 *  ----      ----             ----
 *
 * The large bins are doubly linked and circular. Each node has a varying size.
 * The circularity is an implementation convenience - it allows for fewer
 * global variables if we want to do things like tail insertion.
 * Our insertion policy is slightly more complicated here:
 * - If a block is small enough, we insert at the head.
 * - If a block is large enough, we insert at the tail.
 * Experimentally, I found that head insertion for the 32-64 sized bins and
 * tail insertion for the 128-16384 sized bins performs pretty well in terms of
 * throughput while not sacrificing too much utilization.
 *           ----       ----               ----
 * tail <-> |    | <-> |    | <-> ... <-> |    | <-> head
 *           ----       ----               ----
 *           head                          tail
 *
 * To find a block fit when calling malloc, I use a first-fit policy. Starting
 * at the smallest bin size with sufficient capacity for the request, the
 * search traverses through the freelist starting at the head, moving up to
 * the next bin if no match is found.
 *
 * Upon finding a match, we split the block down to the requested size (plus
 * overhead), adding the split off block back into the seglist.
 *
 * O(1) coalescing is implemented with an immediate-coalesce policy, meaning
 * that we coalesce immediately upon a free operation.
 *
 *
 * OPTIMIZATIONS
 * Here I describe in a bulleted fashion the most significant performance
 * improvements. Much of this information is contained in the above
 * overview of the system.
 *
 * - Segmented list of freelists. This approximates a best fit policy well
 *   enough that we can get away with a fast first-fit policy for finding
 *   free blocks. This improves both utilization and throughput.
 *
 * - No footers for small blocks, instead we use a bit in the header that
 *   indicates the allocations status of the previous block. This improves
 *   utilization.
 *
 * - Singly linked list for small blocks i.e. only the header and one
 *   next pointer. This improves utilization.
 *
 * - A mixture of LIFO and FIFO insertion policies in large bins depending
 *   on the size of the bin. This increases throughput with a negligible
 *   decrease in utilization.
 *
 * FUTURE IMPROVEMENTS
 * - In theory, a search tree would help with utilization for bins that
 *   have high entropy in their distribution of block sizes. This tends
 *   to be the case for the largest bins (recall that the allocation
 *   sizes tend to follow a power-law distribution and the large bins
 *   exist in the tail regime of this distribution). This would allow
 *   an efficient best-fit policy for these bins.
 *
 * FAILED EXPERIMENTS
 * - Splay trees to order blocks by size did not seem to help. In fact,
 *   utilization did not seem to improve while throughput significantly
 *   decreased. I suspect this was due to the overhead of the splay
 *   operation after every insertion and deletion.
 *   Note: I used a best-fit policy for the splay tree.
 *
 *************************************************************************
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h> // uintptr_t
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/*********** Heap checker constants ***********/

/** @brief Return codes for heap checking */
#define BLOCK_VALID (0)
#define ADDRESS_ALIGNMENT_ERROR (1)
#define OUT_OF_BOUNDS_ERROR (1 << 1)
#define SIZE_ERROR (1 << 2)

/** @brief Return codes for the heap checker. */
enum CheckheapCodes { HEAP_INVALID, HEAP_VALID };

/** @brief Convenience type for heap checking return codes. */
typedef uint8_t code_t;

/*********** Basic constants ***********/

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/**
 * @brief Minimum block size (bytes)
 *
 * We need to also allocate space for freelist next and prev pointers, so make
 * extra space for that overhead.
 */
static const size_t min_block_size = dsize;

/**
 * chunksize is the smallest amount of memory that we extend the heap by.
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * alloc_mask is the bitmask for the bit that indicates if the block is
 * allocated.
 */
static const word_t alloc_mask = 0x1;

/** @brief bitmask for the bit that indicates if the previous block is
 * allocated. */
static const word_t prev_alloc_mask = 0x2;

/** @brief bitmask for the bit that indicates if the previous block is small. */
static const word_t prev_small_mask = 0x4;

/**
 * size_mask is the bitmask for the bits that indicate the size of this block.
 */
static const word_t size_mask = ~(word_t)0xF;

/*********** Data structures ***********/

/**
 * @brief Represents the header and payload of one block in the heap
 *
 * @param  header   Contains the size and allocation status (lowest bit) of the
 * block.
 * @param  next     Pointer to the next block in the freelist. Note that this
 * pointer is used for both large and small blocks.
 * @param  prev     Pointer to the previous block in the freelist.
 * @param  payload  Pointer to the actual payload of the block.
 */
typedef struct block block_t;
struct block {
    // Header contains size + allocation + prev_alloc + prev_small bits.
    word_t header;

    union {
        // Linked list overhead.
        struct {
            block_t *next;
            block_t *prev;
        };
        // A pointer to the block payload.
        char payload[0];
    };
};

/** @brief Size of the header for a block. */
static const size_t hsize = offsetof(block_t, payload);

/** @brief Main use: `mem_heap_hi() - hoffset`. */
static const size_t hoffset = hsize - 1;

/** @brief Metadata about the configuration of the seglist. Small bins are those
 * which only use a next pointer rather than next/prev pointers and a footer. We
 * can easily allow multiple block sizes like this if we so desire. */
static const size_t seglist_size = 15;
static const size_t seglist_small_bins = 0; // Bins up to this one are small.
static const size_t seglist_bin_sizes[seglist_size - 1] = {
    min_block_size, 32,   40,   48,   56,   64, 128, 256, 512,
    1024,           2048, 4096, 8192, 16384};

/**
 * @brief If the block size is less than this, we will insert at the tail.
 * Otherwise, we'll insert at the head.
 *
 * I selected this value through multiple benchmarking sessions.
 */
static const size_t seglist_fifo_insertion_threshold = 6;

/*********** Global variables ***********/

/** @brief List of pointers to the head of each doubly circular linked freelist
 * in the seglist. Note that since the list is circular, there is no need to
 * explicitly store tail pointers. */
static block_t *seglist_heads[seglist_size];

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/*********** Function forward declarations ***********/

static block_t *find_next(block_t *block);
static void freelist_insert(block_t *block, const size_t bin);
static size_t seglist_find_bin(block_t *block);
static size_t seglist_find_bin_from_size(size_t size);
extern bool mm_checkheap(int line);

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/*********** Math & misc. helpers ***********/

/**
 * @brief Returns the maximum of two integers.
 *
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Convert a pointer to an numerical value that can be logically
 * compared.
 *
 * The void* argument type will allow for arbitrary pointers to be fed in.
 *
 * @param[in]  ptr  Pointer to convert into numerical value.
 */
uintptr_t ptou(void *ptr) {
    return (uintptr_t)ptr;
}

/*********** Get data ***********/

/**
 * @brief Extract the bit from the header that indicates if the previous block
 * in the implicit list is a small block.
 *
 * @param[in]  word  block_t header.
 * @return true if previous block is small.
 */
static bool extract_prev_small(word_t word) {
    return !!(word & prev_small_mask);
}

/**
 * @brief Extract the bit from a header that indicates if the previous block in
 * the implicit list is allocated.
 *
 * @param[in]  word  block_t header.
 * @return true if the previous block is allocated.
 */
static bool extract_prev_alloc(word_t word) {
    return !!(word & prev_alloc_mask);
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Get the bit from a block that indicates if the previous block in the
 * implicit list is a small block.
 *
 * @param[in]  block  Pointer to a block_t struct.
 * @return true if previous block is small.
 */
static bool get_prev_small(block_t *block) {
    return extract_prev_small(block->header);
}

/**
 * @brief Get the bit from a block that indicates if the previous block in the
 * implicit list is allocated.
 *
 * @param[in]  block  Pointer to a block_t struct.
 * @return true if the previous block is allocated.
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 *
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Extracts the size of a block from its header.
 *
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header.
 *
 * We don't need to account for the footer size here because there is no footer
 * for allocated blocks.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    return get_size(block);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 *
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 *
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 *
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 *
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/*********** Set data ***********/

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc)
        word |= alloc_mask;
    return word;
}

/**
 * @brief Set the bit of the block header that indicates if the previous block
 * in the implicit list is a small block.
 *
 * @param[out]  block       Pointer to a block_t struct.
 * @param[in]   prev_small  State of the bit to write.
 */
static void write_prev_small(block_t *block, bool prev_small) {
    if (prev_small)
        block->header |= prev_small_mask;
    else
        block->header &= ~prev_small_mask;
}

/**
 * @brief Set the bit of the block header that indicates if the previous block
 * in the implicit list is allocated.
 *
 * @param[out]  block       Pointer to a block_t struct.
 * @param[in]   prev_alloc  State of the bit to write.
 */
static void write_prev_alloc(block_t *block, bool prev_alloc) {
    if (prev_alloc)
        block->header |= prev_alloc_mask;
    else
        block->header &= ~prev_alloc_mask;
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - hoffset);

    block->header = pack(0, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * The block must not be an epilogue.
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);

    // State to update / preserve.
    bool small = (size == min_block_size);
    bool prev_small = get_prev_small(block);
    bool prev_alloc = get_prev_alloc(block);

    block->header = pack(size, alloc);

    // Preserve previous state.
    write_prev_alloc(block, prev_alloc);
    write_prev_small(block, prev_small);

    // Update state of next block wrt new state of this one.
    block_t *next = find_next(block);
    write_prev_alloc(next, alloc);
    write_prev_small(next, small);

    // Only free, sufficiently large blocks will contain footers.
    if (!alloc && !small) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc);
    }
}

/*********** Basic search ***********/

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 *
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);

    // Need to handle small blocks differently because we don't have a footer to
    // use. In this case, we assume fixed block size.
    size_t small = get_prev_small(block);
    if (small)
        return (block_t *)(&(block->header) - (min_block_size / wsize));

    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0)
        return NULL;

    return footer_to_header(footerp);
}

/*********** Freelist helpers ***********/

/**
 * @brief Find the next block in the freelist.
 *
 * @note The freelist is circular, so this can wrap around.
 *
 * @note This function used to be more complicated before I implemented
 * next/prev pointers as members of the block struct.
 *
 * @param[in]  block  Must be a block already in the freelist.
 * @return Pointer to the next free block.
 */
static block_t *freelist_find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    dbg_requires(get_size(block));

    return block->next;
}

/**
 * @brief Find the previous block in the freelist.
 *
 * @note The freelist is circular, so this can wrap around.
 *
 * @note This function used to be more complicated before I implemented
 * next/prev pointers as members of the block struct.
 *
 * @param[in]  block  Must be a block already in the freelist.
 * @return Pointer to the previous free block.
 */
static block_t *freelist_find_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    dbg_requires(get_size(block));

    return block->prev;
}

/**
 * @brief Check if a block currently exists in the freelist.
 *
 * @note A utility function for debugging purposes only.
 *
 * @param[in]  block  Pointer to query block.
 * @param[in]  head   Pointer to the head of the freelist to search.
 * @return `true` if the block is in the freelist, `false` otherwise.
 */
static bool is_block_in_freelist(block_t *block, block_t *head) {
    bool looped = false;
    block_t *b = head;

    while (!looped && b != NULL) {
        if (b == block)
            return true;

        b = freelist_find_next(b);
        looped = (b == head);
    }

    return false;
}

/**
 * @brief Set the next pointer of the `block` to `next`.
 *
 * @note This function used to be more complicated before I implemented
 * next/prev pointers as members of the block_t struct.
 *
 * @param[out]  block  Pointer to the block whose next pointer will be updated.
 * Must exist in the freelist.
 * @param[in]   next   Pointer to the block to set the next pointer of `block`
 * to.
 */
static void freelist_set_next(block_t *block, block_t *next) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    dbg_requires(get_size(block));

    block->next = next;
}

/**
 * @brief Set the previous pointer of the `block` to `prev`.
 *
 * @note This function used to be more complicated before I implemented
 * next/prev pointers as members of the block_t struct.
 *
 * @param[out]  block  Pointer to the block whose previous pointer will be
 * updated. Must exist in the freelist.
 * @param[in]   prev   Pointer to the block to set the previous pointer of
 * `block` to.
 */
static void freelist_set_prev(block_t *block, block_t *prev) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    dbg_requires(get_size(block));

    block->prev = prev;
}

/**
 * @brief Remove a block from the freelist.
 *
 * @param[out]  block  Pointer to the block to remove. Must exist in the
 * freelist.
 * @param[in]   bin    Index into the seglist where block lives.
 */
static void freelist_remove(block_t *block, const size_t bin) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    dbg_requires(get_size(block));

    // Small block case.
    // Singly linked list deletion.
    if (bin <= seglist_small_bins) {
        if (block == seglist_heads[bin]) {
            seglist_heads[bin] = freelist_find_next(block);
            return;
        }

        block_t *prev = seglist_heads[bin];
        for (; freelist_find_next(prev) != block;
             prev = freelist_find_next(prev))
            ; // wow that's ugly, thanks clang formatting
        freelist_set_next(prev, freelist_find_next(block));

        return;
    }

    // Large block case.
    // Doubly linked list deletion.
    if (freelist_find_next(block) == block) {
        // Special case: freelist becomes empty.
        seglist_heads[bin] = NULL;

    } else {
        block_t *next = freelist_find_next(block);
        block_t *prev = freelist_find_prev(block);

        freelist_set_next(prev, next);
        freelist_set_prev(next, prev);

        // If block was on the boundary, update the circular edge.
        if (block == seglist_heads[bin])
            seglist_heads[bin] = next;
    }

    dbg_ensures(!is_block_in_freelist(block, seglist_heads[bin]));
}

/**
 * @brief Insert new free block into a freelist indexed by a seglist bin.
 *
 * We insert larger blocks at the end of the list and smaller blocks at the
 * beginning. Assuming a first-fit policy, this will improve utilization
 * slightly by very crudely approximating a best fit policy.
 *
 * @param[out]  block  Pointer to the block to insert. Must not exist in the
 * freelist already.
 * @param[in]   bin    Index into the seglist where block will be inserted.
 */
static void freelist_insert(block_t *block, const size_t bin) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    dbg_requires(get_size(block));
    dbg_requires(!is_block_in_freelist(block, seglist_heads[bin]));

    // Handle small block case separately.
    // LIFO insertion policy.
    if (bin <= seglist_small_bins) {
        // Empty freelist.
        if (seglist_heads[bin] == NULL) {
            seglist_heads[bin] = block;
            freelist_set_next(block, NULL);
            // Otherwise just deal with it like a standard singly linked list.
        } else {
            freelist_set_next(block, seglist_heads[bin]);
            seglist_heads[bin] = block;
        }
        return;
    }

    // Initialize block pointer data to NULL.
    freelist_set_next(block, NULL);
    freelist_set_prev(block, NULL);

    if (seglist_heads[bin] == NULL) {
        seglist_heads[bin] = block;
        freelist_set_next(seglist_heads[bin], block);
        freelist_set_prev(seglist_heads[bin], block);

        dbg_ensures(is_block_in_freelist(block, seglist_heads[bin]));
        return;
    }

    // ---------- FIFO insertion: insert at end of list.
    // If the block size is large enough, then place at the end of the bin's
    // freelist.
    if (bin > seglist_fifo_insertion_threshold) {
        block_t *tail_orig = freelist_find_prev(seglist_heads[bin]);

        freelist_set_next(block, seglist_heads[bin]);
        freelist_set_prev(seglist_heads[bin], block);

        freelist_set_prev(block, tail_orig);
        freelist_set_next(tail_orig, block);

        // --------- LIFO insertion: insert at beginning of list.
        // If the block size is small enough, place at the beginning of the
        // bin's freelist.
    } else {
        block_t *tail = freelist_find_prev(seglist_heads[bin]);

        freelist_set_next(tail, block);
        freelist_set_prev(block, tail);

        freelist_set_next(block, seglist_heads[bin]);
        freelist_set_prev(seglist_heads[bin], block);

        seglist_heads[bin] = block;
    }

    dbg_ensures(is_block_in_freelist(block, seglist_heads[bin]));
}

/*********** Seglist helpers ***********/

/**
 * @brief Find the bin index associated with a given size.
 *
 * @param[in]  size  Size to map to a bin index.
 * @return Index into the seglist.
 */
static size_t seglist_find_bin_from_size(size_t size) {
    dbg_requires(seglist_size);

    size_t bin = 0;
    for (; bin < seglist_size - 1; ++bin)
        if (size <= seglist_bin_sizes[bin])
            return bin;

    return bin; // Return last bin index
}

/**
 * @brief Find the bin index associated with a given block.
 *
 * @note Calls seglist_find_bin_from_size implicitly.
 *
 * @param[in]  block  Pointer to block in the seglist.
 * @return Index into the seglist.
 */
static size_t seglist_find_bin(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(seglist_size);

    return seglist_find_bin_from_size(get_size(block));
}

/**
 * @brief Check if a block is in the seglist.
 *
 * Only for debugging purposes.
 *
 * @note Calls is_block_in_freelist.
 *
 * @param[in]  block  Pointer to query block.
 * @return true if the block is in the seglist, false otherwise.
 */
static bool is_block_in_seglist(block_t *block) {
    const size_t bin = seglist_find_bin(block);
    return is_block_in_freelist(block, seglist_heads[bin]);
}

/**
 * @brief Insert a block into the seglist.
 *
 * @note Calls freelist_insert.
 *
 * @param[in]  block  Pointer to the block to insert. Must not exist in the
 * seglist already.
 */
static void seglist_insert(block_t *block) {
    dbg_requires(!is_block_in_seglist(block));

    const size_t bin = seglist_find_bin(block);
    freelist_insert(block, bin);
}

/**
 * @brief Remove a block from the seglist.
 *
 * @note Calls freelist_remove.
 *
 * @param[in]  block  Pointer to the block to remove. Must already exist in the
 * seglist.
 */
static void seglist_remove(block_t *block) {
    dbg_requires(is_block_in_seglist(block));

    const size_t bin = seglist_find_bin(block);
    freelist_remove(block, bin);
}

/*
 * ---------------------------------------------------------------------------
 *                        END HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Given a pointer to a free block, inspect its left and right neighbors
 * and merge if they are also free.
 *
 * The block must be neither allocated nor an prologue/epilogue block.
 *
 * @param[in]  block  Pointer to a non-allocated block.
 * @return  Pointer to the new coalesced block.
 */
static block_t *coalesce_block(block_t *block) {
    dbg_requires(!get_alloc(block));
    dbg_requires(get_size(block));
    dbg_requires(is_block_in_seglist(block));

    size_t adj_size;
    size_t block_size = get_size(block);

    block_t *next = find_next(block);

    bool prev_alloc = get_prev_alloc(block);
    block_t *prev = NULL;
    if (!prev_alloc)
        prev = find_prev(block);

    // First coalesce right.
    // Keep track of the size of the current block, too.
    if (next && (adj_size = get_size(next)) && !get_alloc(next)) {
        seglist_remove(next);
        seglist_remove(block);

        block_size += adj_size;
        write_block(block, block_size, false);

        seglist_insert(block);
    }

    // Finally, coalesce left.
    if (prev && (adj_size = get_size(prev))) {
        seglist_remove(prev);
        seglist_remove(block);

        block = prev;

        block_size += adj_size;
        write_block(block, block_size, false);

        seglist_insert(block);
    }

    dbg_ensures(mm_checkheap(__LINE__));
    return block;
}

/**
 * @brief Add a new free block of `size` bytes to the heap.
 *
 * @note May add more than the requested number of bytes due to the double word
 * alignment policy.
 *
 * @param[in]  size  Minimum number of bytes to add to the heap.
 * @return Pointer to the new block.
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    // @note `mem_sbrk` will return a pointer to the first byte of the newly
    // allocated heap area.
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    // Initialize free block header/footer
    // @note Write at one word prior b/c we want to overwrite the with the new
    // header.
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Update freelist.
    seglist_insert(block);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return block;
}

/**
 * @brief Split an allocated block into a block of size `asize` and a free block
 * of size `block_size - asize`.
 *
 * Preconditions:
 * - Block must be allocated.
 * - `asize` must not exceed `get_size(block)`.
 *
 * @param[in]  block  Pointer to allocated block.
 * @param[in]  asize  Size to reduce `block` to.
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    dbg_requires(!is_block_in_seglist(block));
    dbg_requires(asize <= get_size(block));

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true);

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);

        dbg_requires(!is_block_in_seglist(block_next));
        seglist_insert(block_next);

        dbg_ensures(get_size(block) == asize);
        dbg_ensures(!get_alloc(block_next));
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief Search for a free block whose capacity is at least as large as the
 * requested size.
 *
 * First fit policy.
 *
 * @param[in]  asize  Requested number of bytes.
 * @return Pointer to a free block with sufficient capacity. If none exists in
 * the heap, return NULL.
 */
static block_t *find_fit(size_t asize) {
    // Large block case.
    for (size_t bin = seglist_find_bin_from_size(asize); bin < seglist_size;
         ++bin) {

        block_t *b = seglist_heads[bin];
        bool looped = false;
        while (!looped && b != NULL) {
            // First-fit policy
            if (asize <= get_size(b))
                return b;

            b = freelist_find_next(b);
            looped = (b == seglist_heads[bin]);
        }
    }
    return NULL; // no fit found
}

/**
 * @brief Initialize the heap, including global variables associated thereof.
 *
 * @return `true` if initialization was successful, `false` otherwise.
 */
bool mm_init(void) {
    // Initialize the seglist freelists to empty.
    for (size_t bin = 0; bin < seglist_size; ++bin)
        seglist_heads[bin] = NULL;

    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * hsize));

    if (start == (void *)-1)
        return false;

    start[0] = pack(0, true); // Heap prologue (block footer)
    start[1] = pack(0, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Mark prologue/epilogue as allocated to indicate heap boundaries.
    write_prev_alloc(heap_start, true);
    write_prev_alloc((block_t *)(mem_heap_hi() - hoffset), true);

    // Extend the empty heap with a free block of chunksize bytes.
    // @note `extend_heap` updates the freelist via insertion.
    if (extend_heap(chunksize) == NULL)
        return false;

    return true;
}

/**
 * @brief Returns a memory block of size at least `size`. May return NULL if
 * such a block cannot be acquired.
 *
 * @param[in]  size  The size in bytes of the requested block.
 * @return Pointer to the first byte of the requested block.
 */
void *mm_malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL)
        mm_init();

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);

        // extend_heap returns an error
        if (block == NULL)
            return bp;
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Update freelist.
    // We need to do this before writing the block so that it isn't marked as
    // allocated.
    seglist_remove(block);

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief Frees a previously allocated (by mm_malloc) block of memory.
 *
 * @note Will fail if the pointer is not one that was returned by mm_malloc at some
 * previous point.
 *
 * @param[in]  bp  Pointer to the first byte of a block of memory returned by
 * mm_malloc.
 */
void mm_free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL)
        return;

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);

    // Update freelist
    seglist_insert(block);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief Resize a previously allocated block.
 *
 * This will search for an unallocated block of sufficient size and copy the
 * bytes of the previously allocated block into the new block, freeing the
 * previously allocated block afterwards.
 *
 * @param[in]  ptr   Pointer to a previously allocated block.
 * @param[in]  size  The new size of the block.
 * @return Pointer to the new, resized block.
 */
void *mm_realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to mm_malloc
    if (ptr == NULL)
        return mm_malloc(size);

    // Otherwise, proceed with reallocation
    newptr = mm_malloc(size);

    // If mm_malloc fails, the original block is left untouched
    if (newptr == NULL)
        return NULL;

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize)
        copysize = size;
    memcpy(newptr, ptr, copysize);

    // Free the old block
    mm_free(ptr);

    return newptr;
}

/**
 * @brief Call mm_malloc and initialize the bits of the allocated block to zero.
 *
 * @param[in]  elements  Number of elements that will be contained in the
 * allocated block.
 * @param[in]  size      The number of bytes per element.
 * @return Pointer to the zero-initialized, allocated block.
 */
void *mm_calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0)
        return NULL;

    if (asize / elements != size)
        // Multiplication overflowed
        return NULL;

    bp = mm_malloc(asize);
    if (bp == NULL)
        return NULL;

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN DEBUGGING FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Print a representation of the heap to stdout.
 *
 * Used for debugging purposes only.
 */
void print_heap(void) {
    for (block_t *block = heap_start; get_size(block) > 0;
         block = find_next(block)) {
        printf(
            "(block %p) alloc %i | prev alloc %i | prev small %i | size %lu\n",
            block, get_alloc(block), get_prev_alloc(block),
            get_prev_small(block), get_size(block));
    }
}

/**
 * @brief Print a representation of the freelist.
 *
 * Only for debugging purposes.
 *
 * @param[in]  head  Pointer to the head of the freelist to print.
 */
void print_freelist(block_t *head) {
    block_t *b = head;
    bool looped = false;
    while (!looped && b != NULL) {
        if (b)
            printf("%p (%lu) (%lu) <-> ", b, seglist_find_bin(b), get_size(b));
        else
            printf("NULL <-> ");

        b = freelist_find_next(b);
        looped = (b == head);
    }
}

/**
 * @brief Print a representation of the seglist.
 *
 * Only for debugging purposes.
 *
 * @note Calls print_freelist implicitly.
 */
void print_seglist(void) {
    printf("\n");
    for (size_t bin = 0; bin < seglist_size; ++bin) {
        if (bin <= seglist_small_bins)
            printf("(small) ");
        else
            printf("(  seg) ");

        printf("bin %lu (%lu):\t", bin,
               (bin < seglist_size - 1) ? seglist_bin_sizes[bin] : SIZE_MAX);
        print_freelist(seglist_heads[bin]);
        printf("\n");
    }
}

/**
 * @brief Check a block in the implicit list and return a code indicating its
 * status.
 *
 * Corresponding codes are returned depending on which (if any) of the required
 * conditions are violated. See `implicit_list_checker` for more details.
 *
 * @param[in]  block  Pointer to the block to check.
 * @return Code BLOCK_VALID (zero-value) if no error is detected. Otherwise, a
 * nonzero value code is returned indicating the detected error.
 */
code_t check_block_validity(block_t *block) {
    code_t code = BLOCK_VALID;

    if ((word_t)header_to_payload(block) % dsize)
        code |= ADDRESS_ALIGNMENT_ERROR;

    if (ptou(block) < ptou(mem_heap_lo()) ||
        ptou(block) > ptou(mem_heap_hi() - hoffset))
        code |= OUT_OF_BOUNDS_ERROR;

    if (get_size(block) < min_block_size)
        code |= SIZE_ERROR;

    return code;
}

/**
 * @brief Check that the implicit list of the heap is consistent.
 *
 * Will check the following:
 * - That the payload address is aligned properly.
 * - That the block address is within heap bounds.
 * - That the block is at least as big as `min_block_size`.
 * - That the header and footer are consistent.
 *
 * @param[in]  line     Line number from which mm_checkheap was called.
 * @return HEAP_VALID (true) if no error is detected, HEAP_INVALID (false)
 * otherwise.
 */
bool implicit_list_checker(int line) {
    bool ret_code = HEAP_VALID;
    size_t block_idx = 0;
    bool alloc_prev = true;
    bool small_prev = true;

    for (block_t *block = heap_start; get_size(block) > 0;
         block = find_next(block)) {
        // Check if block is valid.
        code_t code = check_block_validity(block);
        if (code & ADDRESS_ALIGNMENT_ERROR) {
            fprintf(stderr,
                    "[implicit] (line %i) (block %p) Address "
                    "misalignment %p.\n",
                    line, block, header_to_payload(block));
            ret_code = HEAP_INVALID;
        }
        if (code & OUT_OF_BOUNDS_ERROR) {
            fprintf(stderr,
                    "[implicit] (line %i) (block %p) Block "
                    "out of heap bounds.\n",
                    line, block);
            ret_code = HEAP_INVALID;
        }
        if (code & SIZE_ERROR) {
            fprintf(stderr,
                    "[implicit] (line %i) (block %p) Size %lu "
                    "is smaller than minimum required block size %lu\n",
                    line, block, get_size(block), min_block_size);
            ret_code = HEAP_INVALID;
        }

        // Check that prev_alloc bit is correct.
        if (block_idx && alloc_prev != get_prev_alloc(block)) {
            fprintf(stderr,
                    "[implicit] (line %i) (block %p) Inconsistent "
                    "prev_alloc bit (blocks %lu, %lu).\n",
                    line, block, block_idx - 1, block_idx);
            ret_code = HEAP_INVALID;
        }

        // Check that prev_small bit is correct.
        if (block_idx && small_prev != get_prev_small(block)) {
            fprintf(stderr,
                    "[implicit] (line %i) (block %p) Inconsistent "
                    "prev_small bit (blocks %lu, %lu).\n",
                    line, block, block_idx - 1, block_idx);
            ret_code = HEAP_INVALID;
        }

        // Coalescing check.
        if (block_idx && !alloc_prev && !get_alloc(block)) {
            fprintf(
                stderr,
                "[implicit] (line %i) (block %p) Coalesce "
                "failed -- found consecutive free blocks (blocks %lu, %lu).\n",
                line, block, block_idx - 1, block_idx);
            ret_code = HEAP_INVALID;
        }

        // Update loop variables.
        block_idx++;
        alloc_prev = get_alloc(block);
        small_prev = (get_size(block) <= seglist_bin_sizes[seglist_small_bins]);
    }

    return ret_code;
}

/**
 * @brief Check the blocks in the explicit freelist for consistency.
 *
 * The following conditions are checked:
 * - All blocks are marked as free.
 * - The next/prev pointers are consistent i.e. the prev pointer of the next
 * block is a pointer to this block.
 * - The addresses of all free blocks are within bounds.
 *
 * @param[in]  line     Line number from which mm_checkheap was called.
 * @return HEAP_VALID (true) if no errors detected, HEAP_INVALID (false)
 * otherwise.
 */
static bool explicit_list_checker(int line, block_t *head) {
    bool ret_code = HEAP_VALID;
    bool looped = false;
    block_t *block = head;

    while (!looped && block != NULL) {
        // Make sure all blocks are marked as free.
        if (get_alloc(block)) {
            fprintf(stderr,
                    "[freelist] (line %i) Freelist block "
                    "marked as allocated.\n",
                    line);
            return HEAP_INVALID;
        }

        // Check next/prev pointer consistency.
        if (freelist_find_prev(freelist_find_next(block)) != block) {
            fprintf(stderr,
                    "[freelist] (line %i) Next (%lu) and prev "
                    "(%lu) pointer inconsistency.\n",
                    line, ptou(freelist_find_next(block)),
                    ptou(freelist_find_prev(freelist_find_next(block))));
            return HEAP_INVALID;
        }

        if (freelist_find_next(freelist_find_prev(block)) != block) {
            fprintf(stderr,
                    "[freelist] (line %i) prev (%lu) and next "
                    "(%lu) pointer inconsistency.\n",
                    line, ptou(freelist_find_prev(block)),
                    ptou(freelist_find_next(freelist_find_prev(block))));
            return HEAP_INVALID;
        }

        // Make sure that all blocks are within bounds.
        if (ptou(block) < ptou(heap_start) ||
            ptou(block) > ptou(mem_heap_hi() - hoffset)) {
            fprintf(stderr,
                    "[freelist] (line %i) Freelist block "
                    "(0x%lu) address out of bounds (0x%lu, 0x%lu).\n",
                    line, ptou(block), ptou(heap_start),
                    ptou(mem_heap_hi() - hoffset));
            return HEAP_INVALID;
        }

        // Update loop variables.
        block = freelist_find_next(block);
        looped = (block == head);
    }

    return ret_code;
}

/**
 * @brief Check the seglist for consistency.
 *
 * The following conditions are checked:
 * - The number of free blocks in the seglist matches the number of free blocks
 * in the implicit list.
 * - Each block is placed in the correct bin relative to its size.
 * - All conditions of explicit_list_checker are also checked implicitly.
 *
 * @note This function calls explicit_list_checker.
 *
 * @param[in]  line     The line number from which mm_checkheap was called.
 * @return HEAP_VALID (true) if no errors detected, HEAP_INVALID otherwise.
 */
static bool seglist_checker(int line) {
    bool ret_code = HEAP_VALID;
    size_t num_free_blocks_explicit = 0;

    for (size_t bin = 0; bin < seglist_size; ++bin) {
        size_t bin_size_upper =
            (bin < seglist_size - 1) ? seglist_bin_sizes[bin] : SIZE_MAX;
        size_t bin_size_lower = bin ? seglist_bin_sizes[bin - 1] : 0;
        if (bin <= seglist_small_bins)
            bin_size_upper = bin_size_lower = seglist_bin_sizes[bin];

        size_t block_idx = 0;
        bool looped = false;
        block_t *b = seglist_heads[bin];
        while (!looped && b != NULL) {
            // Check that all blocks in bin are appropriately sized.
            if (bin <= seglist_small_bins) {
                if (get_size(b) != seglist_bin_sizes[bin]) {
                    fprintf(stderr,
                            "(line %i) (small) Block %p size "
                            "%lu does not match small bin size %lu.\n",
                            line, b, get_size(b), seglist_bin_sizes[bin]);
                    print_seglist();
                    return HEAP_INVALID;
                }
            } else if (get_size(b) > bin_size_upper ||
                       get_size(b) <= bin_size_lower) {
                fprintf(stderr,
                        "(line %i) (bin %lu block %lu) Block "
                        "size (%lu) not in bin range [%lu, %lu].\n",
                        line, bin, block_idx, get_size(b), bin_size_lower,
                        bin_size_upper);
                print_seglist();
                return HEAP_INVALID;
            }

            // Check that bin selection for the block is consistent.
            if (seglist_find_bin(b) != bin) {
                fprintf(stderr,
                        "(line %i) (bin %lu block %lu) Block "
                        "bin is %lu but seglist_find_bin returned %lu.\n",
                        line, bin, block_idx, bin, seglist_find_bin(b));
                print_seglist();
                return HEAP_INVALID;
            }

            if (bin <= seglist_small_bins && find_next(b) &&
                !get_prev_small(find_next(b))) {
                fprintf(stderr,
                        "(line %i) (small blocks) Block %p "
                        "next block has prev_small bit set to 0.\n",
                        line, b);
                print_seglist();
                return HEAP_INVALID;
            }

            b = freelist_find_next(b);
            looped = (b == seglist_heads[bin]);
            block_idx++;
            num_free_blocks_explicit++;
        }
    }

    // Count the number of free blocks from view of implicit list.
    size_t num_free_blocks_implicit = 0;
    for (block_t *block = heap_start; get_size(block) > 0;
         block = find_next(block))
        if (!get_alloc(block))
            num_free_blocks_implicit++;

    if (num_free_blocks_implicit != num_free_blocks_explicit) {
        fprintf(stderr,
                "(line %i) Inconsistent number of free blocks "
                "(implicit %lu, explicit %lu).\n",
                line, num_free_blocks_implicit, num_free_blocks_explicit);
        return HEAP_INVALID;
    }

    return ret_code;
}

/**
 * @brief Check that the heap is valid. Useful for debugging.
 *
 * @param[in]  line  Line number from which `mm_checkheap` was called.
 * @return `false` if a heap error is detected, `false` otherwise.
 */
bool mm_checkheap(int line) {
    //--------------------------------------------------
    // Check generic heap invariants.
    //--------------------------------------------------
    bool ret_code = HEAP_VALID;

    // Check for prologue block.
    block_t *start = mem_heap_lo();
    if (get_size(start) && !get_prev_alloc(find_next(start))) {
        fprintf(stderr, "(line %i) No prologue boundary.\n", line);
        return HEAP_INVALID;
    }

    // Check for epilogue block.
    block_t *end = mem_heap_hi() - hoffset;
    if (!get_alloc(end) || get_size(end)) {
        fprintf(stderr, "(line %i) No epilogue boundary.\n", line);
        return HEAP_INVALID;
    }

    if (heap_start == NULL) {
        fprintf(stderr,
                "(line %i) Heap has not been initialized "
                "(heap_start is NULL).\n",
                line);
        return HEAP_INVALID;
    }

    //--------------------------------------------------
    // Check list implementation-specific heap invariants.
    //--------------------------------------------------
    // Check implicit list for consistency.
    if (implicit_list_checker(line) == HEAP_INVALID)
        return HEAP_INVALID;

    // Check explicit list for consistency.
    if (seglist_checker(line) == HEAP_INVALID)
        return HEAP_INVALID;

    return ret_code;
}

/*
 * ---------------------------------------------------------------------------
 *                        END DEBUGGING FUNCTIONS
 * ---------------------------------------------------------------------------
 */
