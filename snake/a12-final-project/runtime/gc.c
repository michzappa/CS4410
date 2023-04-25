#include "snakeval.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/// Global variables relating to heap accessible to both C runtime and Snake
/// runtime
uint64_t* heap_alloc_ptr;
uint64_t* heap_base_ptr;
uint64_t* heap_end_ptr;
size_t    heap_size;
uint64_t* heap_cursor;

ss_bin_tree_t string_map;

static uint8_t string_visit_idx;

typedef struct {
  const uint64_t* snake_stack_bottom;

  uint64_t* top_base_ptr;
  uint64_t* top_stack_ptr;

  const uint64_t* old_base_ptr;
  const uint64_t* old_end_ptr;
  const uint64_t* new_base_ptr;
  const uint64_t* new_end_ptr;
} gc_context_t;

typedef struct {
  size_t     size_and_tag;
  snakeval_t values[];
} heap_tuple_like_t;

typedef struct {
  size_t     arity_and_tag;
  uint64_t   untouched;
  size_t     num_values;
  snakeval_t values[];
} heap_closure_like_t;

typedef struct {
  size_t    size_and_tag;
  uintptr_t char_ptr;
} heap_string_like_t;

typedef enum heap_like_type {
  TUPLE_LIKE,
  CLOSURE_LIKE,
  STRING_LIKE,
} heap_like_type_t;

typedef struct {
  union {
    heap_tuple_like_t*   tuple;
    heap_closure_like_t* closure;
    heap_string_like_t*  string;
  };
  heap_like_type_t heap_type;
} heap_like_t;

#define HEAP_TUPLE_LIKE_TAG_MASK   0x8000000000000000UL
#define HEAP_CLOSURE_LIKE_TAG_MASK 0xc000000000000000UL
#define HEAP_STRING_LIKE_TAG_MASK  0xc000000000000000UL

#define HEAP_TUPLE_LIKE_TAG   0x0000000000000000UL
#define HEAP_CLOSURE_LIKE_TAG 0x8000000000000000U
#define HEAP_STRING_LIKE_TAG  0xc000000000000000U

#define HEAP_IS_TUPLE_LIKE(_val_)   SV_IS_TYPE(_val_, HEAP_TUPLE_LIKE)
#define HEAP_IS_CLOSURE_LIKE(_val_) SV_IS_TYPE(_val_, HEAP_CLOSURE_LIKE)
#define HEAP_IS_STRING_LIKE(_val_)  SV_IS_TYPE(_val_, HEAP_STRING_LIKE)

static heap_like_t heap_obj_to_heap_like(uint64_t* heap_obj) {
  // heap_obj is pointing to the heap and must point to the start either a tuple
  // or closure like object
  if (HEAP_IS_TUPLE_LIKE(*heap_obj)) {
    heap_tuple_like_t* ptr;
    memcpy(&ptr, &heap_obj, sizeof(ptr));
    heap_like_t heap_like = {
        .tuple     = ptr,
        .heap_type = TUPLE_LIKE,
    };
    return heap_like;
  }
  if (HEAP_IS_CLOSURE_LIKE(*heap_obj)) {
    heap_closure_like_t* ptr;
    memcpy(&ptr, &heap_obj, sizeof(ptr));
    heap_like_t heap_like = {
        .closure   = ptr,
        .heap_type = CLOSURE_LIKE,
    };
    return heap_like;
  }
  if (HEAP_IS_STRING_LIKE(*heap_obj)) {
    heap_string_like_t* ptr;
    memcpy(&ptr, &heap_obj, sizeof(ptr));
    heap_like_t heap_like = {
        .string    = ptr,
        .heap_type = STRING_LIKE,
    };
    return heap_like;
  }
  assert(false);
}

static size_t heap_like_size_in_words(const heap_like_t heap_like) {
  switch (heap_like.heap_type) {
  case TUPLE_LIKE: {
    size_t size = heap_like.tuple->size_and_tag & ~HEAP_TUPLE_LIKE_TAG_MASK;
    size += 1;                    // word for size header
    if (size % 2 == 1) size += 1; // padding word
    return size;
  }
  case CLOSURE_LIKE: {
    size_t size = heap_like.closure->num_values;
    size += 3;                    // word for arith, code ptr, size header
    if (size % 2 == 1) size += 1; // padding word
    return size;
  }
  case STRING_LIKE: return 2;
  }
  assert(false);
}

static bool sv_is_heap_value(const snakeval_t val) {
  switch (sv_type_of(val)) {
  case SV_INVALID:
  case SV_PADDING:
  case SV_BOOL:
  case SV_NUM: return false;
  case SV_CLOSURE:
  case SV_STRING:
  case SV_FWD_PTR: return true;
  case SV_TUPLE: return val != TUPLE_NIL;
  }
  assert(false);
}

static snakeval_t sv_get_maybe_forwarded_value(const snakeval_t val) {
  switch (sv_type_of(val)) {
  case SV_INVALID:
  case SV_PADDING:
  case SV_BOOL:
  case SV_FWD_PTR:
  case SV_NUM: assert(false);
  case SV_TUPLE: {
    if (val == TUPLE_NIL) assert(false);

    const snakeval_t maybe_fwd_ptr = sv_to_tuple_unchecked(val)->values[0];
    if (!SV_IS_FWD_PTR(maybe_fwd_ptr)) return 0;

    snakeval_t fwd_ptr = maybe_fwd_ptr;
    // remove forwarding pointer tag
    fwd_ptr &= ~FWD_PTR_TAG_MASK;
    // re-tag as tuple
    fwd_ptr |= TUPLE_TAG;
    // return the new snakeval for the given snakeval
    return fwd_ptr;
  }
  case SV_CLOSURE: {
    const snakeval_t maybe_fwd_ptr = sv_to_closure_unchecked(val)->free_vars[0];
    if (!SV_IS_FWD_PTR(maybe_fwd_ptr)) return 0;

    snakeval_t fwd_ptr = maybe_fwd_ptr;
    // remove forwarding pointer tag
    fwd_ptr &= ~FWD_PTR_TAG_MASK;
    // re-tag as closure
    fwd_ptr |= CLOSURE_TAG;
    // return the new snakeval for the given snakeval
    return fwd_ptr;
  }
  case SV_STRING: {
    const snakeval_t maybe_fwd_ptr =
        pun_ptoi((const uint64_t*)sv_to_string_unchecked(val)->string);
    if (!SV_IS_FWD_PTR(maybe_fwd_ptr)) return 0;

    snakeval_t fwd_ptr = maybe_fwd_ptr;
    // remove forwarding pointer tag
    fwd_ptr &= ~FWD_PTR_TAG_MASK;
    // re-tag as string
    fwd_ptr |= STRING_TAG;
    // return the new snakeval for the given snakeval
    return fwd_ptr;
  }
  }
  assert(false);
}

/// Prints the contents of the heap, in terms of the word number, the exact
/// address, the hex value at that address and the decimal value at that
/// address. Does not attempt to interpret the words as Garter values
///
/// \param heap_start the starting address of the heap
/// \param heap_end the first address after the heap
static void
naive_print_heap(const uint64_t* heap_start, const uint64_t* heap_end) {
  printf(
      "In naive_print_heap from %p to %p\n",
      (const void*)heap_start,
      (const void*)heap_end
  );
  for (int64_t i = 0; i < (int64_t)(heap_end - heap_start); ++i) {
    printf(
        "  %ld/%p: %p (%ld)\n",
        i,
        (const void*)(heap_start + i),
        (const void*)(*(heap_start + i)),
        *(heap_start + i)
    );
  }
}

/// Copies a Garter value from the given address to the new heap, but only if
/// the value is heap-allocated and needs copying.
///
/// Invariant:
///   The heap must have enough space to copy over the value to the top, this
///   invariant is already satified if called from within gc
///
/// Side effect:
///   If the data needed to be copied, then this replaces the value at its old
///   location with a forwarding pointer to its new location. The moved value
///   is temporarily tagged for breath first traversal of the heap.
///
/// \param val_addr *address* of some Snake value that may need to be copied
/// \param heap_top location at which to begin copying, if any copying is needed
/// \param context garbage collection heap and stack information
/// \return new top of the heap, at which to continue allocations
static uint64_t* copy_if_needed(
    snakeval_t* const         val_addr,
    uint64_t* const           heap_top,
    const gc_context_t* const context
) {
  const snakeval_t val = *val_addr;
  if (!sv_is_heap_value(val)) return heap_top;

  assert(
      TUPLE_TAG_MASK == CLOSURE_TAG_MASK && TUPLE_TAG_MASK == STRING_TAG_MASK
  );
  const uint64_t untagged = val & ~TUPLE_TAG_MASK;
  if (!(untagged >= pun_ptoi(context->old_base_ptr) &&
        untagged < pun_ptoi(context->old_end_ptr))) {
    return heap_top;
  }

  // if the snakeval at val_addr points to a heap object which
  // contains a forwarding pointer, update the snakeval at val_addr
  // and return unchanged heap
  const snakeval_t maybe_found_fwd_ptr =
      sv_get_maybe_forwarded_value(*val_addr);
  if (maybe_found_fwd_ptr != 0) {
    *val_addr = maybe_found_fwd_ptr;
    return heap_top;
  }

  assert(
      TUPLE_TAG_MASK == CLOSURE_TAG_MASK && TUPLE_TAG_MASK == STRING_TAG_MASK
  );
  uint64_t* const heap_ptr = pun_itop(val & ~TUPLE_TAG_MASK);

  if (SV_IS_TUPLE(val)) {
    // tag the 'size' word of tuple-like heap obj
    heap_ptr[0] |= HEAP_TUPLE_LIKE_TAG;
  } else if (SV_IS_CLOSURE(val)) {
    // tag the 'arity' word of closure-like heap obj
    heap_ptr[0] |= HEAP_CLOSURE_LIKE_TAG;
  } else if (SV_IS_STRING(val)) {
    // tag the 'size' word of string-like heap obj
    heap_ptr[0] |= HEAP_STRING_LIKE_TAG;
  } else {
    assert(false);
  }

  const heap_like_t heap_like     = heap_obj_to_heap_like(heap_ptr);
  const size_t      heap_obj_size = heap_like_size_in_words(heap_like);
  // the actual copy
  memcpy(heap_top, heap_ptr, heap_obj_size * sizeof(uint64_t));

  const snakeval_t new_fwd_ptr = pun_ptoi(heap_top) | FWD_PTR_TAG;
  switch (heap_like.heap_type) {
  case TUPLE_LIKE: heap_like.tuple->values[0] = new_fwd_ptr; break;
  case CLOSURE_LIKE: heap_like.closure->values[0] = new_fwd_ptr; break;
  case STRING_LIKE: {
    // Update the string map as live before tagging
    str_metadata_t* md =
        sbt_get_from_ptr(&string_map, (const char*)heap_like.string->char_ptr);
    // If slicing a read only string, it won't be in the map
    if (md != NULL) { md->visit_idx = string_visit_idx; }

    heap_like.string->char_ptr = new_fwd_ptr;
    break;
  }
  }

  // update the value at val_addr to point to the copied object,
  // tagged appropriately
  if (SV_IS_TUPLE(val)) {
    *val_addr = pun_ptoi(heap_top) | TUPLE_TAG;
  } else if (SV_IS_CLOSURE(val)) {
    *val_addr = pun_ptoi(heap_top) | CLOSURE_TAG;
  } else if (SV_IS_STRING(val)) {
    *val_addr = pun_ptoi(heap_top) | STRING_TAG;
  } else {
    assert(false);
  }

  return heap_top + heap_obj_size;
}

/// Implements Cheney's garbage collection algorithm.
///
/// Invariant:
///   The new heap must be large enough to hold all of the old heap
///
/// \param heap_start pointer to new heap start of unused data
/// \param context garbage collection heap and stack information
/// \return new location within the new heap at which to allocate new data
static uint64_t*
gc(uint64_t* const heap_start, const gc_context_t* const context) {
  uint64_t* cur_stack_ptr = context->top_stack_ptr;
  uint64_t* next_rbp      = context->top_base_ptr;
  uint64_t* heap_top      = heap_start;

  // Bump the string visit index but never use zero since that is the init
  string_visit_idx += 1;
  if (string_visit_idx == 0) { string_visit_idx = 1; }

  if (pun_ptoi(cur_stack_ptr) == pun_ptoi(context->snake_stack_bottom)) {
    return heap_top;
  }

  if (cur_stack_ptr == next_rbp) {
    next_rbp = pun_itop(*next_rbp);
    cur_stack_ptr += 2; // skip the saved rbp and return address
  }

  while (true) {
    heap_top = copy_if_needed(cur_stack_ptr, heap_top, context);

    cur_stack_ptr += 1;
    if (pun_ptoi(cur_stack_ptr) == pun_ptoi(context->snake_stack_bottom)) {
      break;
    } else if (pun_ptoi(cur_stack_ptr) == pun_ptoi(next_rbp)) {
      next_rbp = pun_itop(*next_rbp);
      cur_stack_ptr += 2; // skip the saved rbp and return address
    }
  }

  uint64_t* heap_copy_base = heap_start;
  while (heap_copy_base < heap_top) {
    // create heap-like object and drag out metadata
    const heap_like_t heap_like = heap_obj_to_heap_like(heap_copy_base);

    switch (heap_like.heap_type) {
    case STRING_LIKE: {
      // untag first byte of heap-like object
      heap_copy_base[0] &= ~HEAP_STRING_LIKE_TAG_MASK;
      break;
    }
    case TUPLE_LIKE:
    case CLOSURE_LIKE: {
      const size_t num_values =
          heap_like.heap_type == TUPLE_LIKE
              ? heap_like.tuple->size_and_tag & ~HEAP_TUPLE_LIKE_TAG
              : heap_like.closure->num_values;
      snakeval_t* const values = heap_like.heap_type == TUPLE_LIKE
                                   ? heap_like.tuple->values
                                   : heap_like.closure->values;

      // heap object structure -> traverse values
      for (size_t value_index = 0; value_index < num_values; ++value_index) {
        // foreach value -> copy_if_needed
        heap_top = copy_if_needed(&values[value_index], heap_top, context);
      }

      // untag first byte of heap-like object
      heap_copy_base[0] &=
          ~(heap_like.heap_type == TUPLE_LIKE ? HEAP_TUPLE_LIKE_TAG_MASK
                                              : HEAP_CLOSURE_LIKE_TAG_MASK);
      break;
    }
    }
    // bump heap_copy_base
    heap_copy_base += heap_like_size_in_words(heap_like);
  }
  assert(heap_copy_base == heap_top);

  return heap_top;
}

static bool remove_unvisited(string_span_t s, str_metadata_t md) {
  (void)s;
  return md.visit_idx != string_visit_idx;
}

static uint64_t* force_gc(
    const size_t    bytes_needed,
    uint64_t* const cur_base_ptr,
    uint64_t* const cur_stack_ptr
) {
  // Garbage collection is pointless if the value is larger than our heap
  if (bytes_needed / sizeof(uint64_t) > heap_size) {
    fprintf(
        stderr,
        "Allocation error: needed %ld words, but the heap is only %ld words\n",
        bytes_needed / sizeof(uint64_t),
        heap_size
    );
    fflush(stderr);
    error(OUT_OF_MEMORY, 0);
  }

  uint64_t* new_heap = (uint64_t*)calloc(heap_size + 15, sizeof(uint64_t));
  if (new_heap == NULL) {
    fprintf(
        stderr,
        "Calloc error: allocation failed for new semispace garbage "
        "collection\n"
    );
    fflush(stderr);
    error(OUT_OF_MEMORY, 0);
  }

  uint64_t* old_heap = heap_alloc_ptr;

  uint64_t* new_heap_base = pun_itop((pun_ptoi(new_heap) + 15) & ~0xFUL);
  uint64_t* new_heap_end  = new_heap_base + heap_size;

  const gc_context_t context = {
      .snake_stack_bottom = snake_entry_base_pointer,
      .top_base_ptr       = cur_base_ptr,
      .top_stack_ptr      = cur_stack_ptr,
      .old_base_ptr       = heap_base_ptr,
      .old_end_ptr        = heap_end_ptr,
      .new_base_ptr       = new_heap_base,
      .new_end_ptr        = new_heap_end,
  };

  heap_alloc_ptr = new_heap;
  heap_base_ptr  = new_heap_base;
  heap_end_ptr   = new_heap_end;

  heap_cursor = gc(new_heap_base, &context);
  free(old_heap);

  sbt_remove_if(&string_map, remove_unvisited);

  if (heap_cursor + (bytes_needed / sizeof(uint64_t)) > heap_end_ptr) {
    fprintf(
        stderr,
        "Out of memory: needed %ld words, but only %ld remain after "
        "collection\n",
        bytes_needed / sizeof(uint64_t),
        heap_end_ptr - heap_cursor
    );
    fflush(stderr);
    error(OUT_OF_MEMORY, 0);
  }

  uint64_t* saved_hc = heap_cursor;
  heap_cursor        = pun_itop(pun_ptoi(heap_cursor) + bytes_needed);
  return saved_hc;
}

/// Try to reserve the desired number of bytes of memory, and free garbage if
/// needed.  Fail (and exit the program) if there is insufficient memory. Does
/// not actually allocate the desired number of bytes of memory; the caller will
/// do that.
///
/// Side effect:
///   If garbage collection occurs, global variables holding heap base, start,
///   and end will be updated
///
/// \param bytes_needed number of bytes of memory we want to allocate (including
/// padding)
/// \param cur_base_ptr base pointer of the topmost stack frame of our code
/// (RBP)
/// \param cur_stack_ptr stack pointer of the topmost stack frame of our code
/// (RSP)
/// \return new top of the heap (i.e. the new value of R15) after garbage
/// collection. Does not actually allocate bytes_needed space.
uint64_t* try_gc(
    const size_t    bytes_needed,
    uint64_t* const cur_base_ptr,
    uint64_t* const cur_stack_ptr
) {
  // Silence warnings about the debug functions
  (void)naive_print_heap;

  assert(pun_ptoi(heap_cursor) % 16 == 0);
  // Only garbage collect when we run out of memory
  if (pun_ptoi(heap_cursor) + bytes_needed <= pun_ptoi(heap_end_ptr)) {
    uint64_t* saved_hc = heap_cursor;
    heap_cursor        = pun_itop(pun_ptoi(heap_cursor) + bytes_needed);
    return saved_hc;
  }

  return force_gc(bytes_needed, cur_base_ptr, cur_stack_ptr);
}

uint64_t*
reserve_str_gc(uint64_t* const cur_base_ptr, uint64_t* const cur_stack_ptr) {
  const size_t bytes_needed = sizeof(snake_string_t);

  assert(pun_ptoi(heap_cursor) % 16 == 0);
  // Only garbage collect when we run out of memory or string_map is full
  if (pun_ptoi(heap_cursor) + bytes_needed <= pun_ptoi(heap_end_ptr) &&
      string_map.size < string_map.max_capacity) {
    uint64_t* saved_hc = heap_cursor;
    heap_cursor        = pun_itop(pun_ptoi(heap_cursor) + bytes_needed);
    return saved_hc;
  }

  uint64_t* reserved_space =
      force_gc(bytes_needed, cur_base_ptr, cur_stack_ptr);

  if (string_map.size >= string_map.max_capacity) {
    assert(string_map.size == string_map.max_capacity);
    fprintf(
        stderr,
        "Out of string space: string map is full with max capacity %ld\n",
        string_map.max_capacity
    );
    fflush(stderr);
    error(OUT_OF_MEMORY, 0);
  }

  return reserved_space;
}
