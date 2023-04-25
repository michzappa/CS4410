#include "decl.h"
#include "snakeval.h"

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

snakeval_t print_raw(snakeval_t val) {
  printf("0x%016lx ==> %ld\n", val, val);
  return val;
}

/// Prints the value to stdout then returns the same value actings as an
/// identity function
///
/// \param val Snake value to print and return
/// \return Value passed in
snakeval_t print(const snakeval_t val) {
  output_snakeval(val, stdout);
  printf("\n");

  // We should never encounter invalid user types
  snakeval_type_t type = sv_type_of(val);
  assert(type != SV_INVALID && type != SV_PADDING && type != SV_FWD_PTR);

  return val;
}

typedef struct {
  snakeval_t left;
  snakeval_t right;
} equal_cache_t;

static size_t
ensure_cache(equal_cache_t** p_cache, size_t last, size_t size, size_t needed) {
  const size_t minneeded = last + needed;
  if (minneeded < size) return size;

  const size_t doubled = size * 2;
  const size_t newsize = (doubled > minneeded) ? doubled : minneeded;

  equal_cache_t* const newcache =
      (equal_cache_t*)realloc(*p_cache, size * 2 * sizeof(equal_cache_t));
  if (newcache == NULL) {
    fprintf(stderr, "Internal error while trying to compute equality\n");
    fprintf(stderr, "Realloc failed for the cache\n");
    exit(ENOMEM);
  }

  *p_cache = newcache;
  return newsize;
}

/// Implementation of structural equality that uses bool type to easier interact
/// with C.
///
/// \return true iff both values are structurally the same
static bool equal_impl(snakeval_t lhs, snakeval_t rhs) {
  if (lhs == rhs) return true;

  size_t         size  = 100;
  equal_cache_t* cache = (equal_cache_t*)calloc(size, sizeof(equal_cache_t));

  size_t cur       = 0;
  size_t last      = 1;
  bool   ans       = true;
  cache[cur].left  = lhs;
  cache[cur].right = rhs;

  while (cur < last) {
    lhs = cache[cur].left;
    rhs = cache[cur].right;
    cur += 1;

    if (lhs == rhs) continue;
    if (lhs == TUPLE_NIL || rhs == TUPLE_NIL) {
      ans = false;
      break;
    }

    bool found_cached = false;
    for (size_t i = 0; i < cur - 1; ++i) {
      if (cache[i].left == lhs && cache[i].right == rhs) {
        found_cached = true;
        break;
      }
    }

    if (found_cached) continue;
    if (SV_IS_STRING(lhs) && SV_IS_STRING(rhs)) {
      snake_string_t* lhs_str = sv_to_string(lhs);
      snake_string_t* rhs_str = sv_to_string(rhs);

      if (lhs_str->length != rhs_str->length) {
        ans = false;
        break;
      }

      if (memcmp(lhs_str->string, rhs_str->string, lhs_str->length) != 0) {
        ans = false;
        break;
      }

      continue;
    }

    if (!SV_IS_TUPLE(lhs) || !SV_IS_TUPLE(rhs)) {
      ans = false;
      break;
    }

    snake_tuple_t* tup_lhs = sv_to_tuple(lhs);
    snake_tuple_t* tup_rhs = sv_to_tuple(rhs);
    if (tup_lhs->size != tup_rhs->size) {
      ans = false;
      break;
    }

    size = ensure_cache(&cache, last, size, tup_lhs->size);
    for (size_t i = 0; i < tup_lhs->size; ++i) {
      cache[last].left  = tup_lhs->values[i];
      cache[last].right = tup_rhs->values[i];
      last += 1;
    }
  }

  free(cache);
  return ans;
}

/// Performs check for structural equality of two snake values from snake
/// runtime values. Short circuit on direct comparison of the values, then
/// filter it down to just tuple equality. Tuple equality checks that size match
/// and then recursive checks each element of the two values.
///
/// \return snake true iff both values are structurally the same, else snake
/// false
snakeval_t equal(const snakeval_t lhs, const snakeval_t rhs) {
  return bool_to_sv(equal_impl(lhs, rhs));
}

/// Asserts that the given tuple has the given length. Errors if not given a
/// non-nil tuple or a positive number. Errors when the tuple length does not
/// match. Returns the given tuple on success.
///
/// \param tuple snake value tuple to check the length
/// @param length expected length to compare against
/// @return input tuple unmodified
snakeval_t assert_tuple_len(const snakeval_t tuple, const snakeval_t length) {
  // Verify non nil tuple and number for length
  if (!SV_IS_TUPLE(tuple)) error(ACCESS_NOT_TUPLE, tuple);
  if (tuple == TUPLE_NIL) error(NIL_DEREF, 0);
  if (!SV_IS_NUM(length)) error(INDEX_NOT_NUM, length);

  const snake_tuple_t* const tup = sv_to_tuple(tuple);
  const int64_t              len = sv_to_int(length);

  // Verify that the length argument is positive
  if (len < 0) {
    fprintf(stderr, "expected positive number: %ld\n", len);
    exit(EXIT_FAILURE);
  }

  // Verify that the tuple size matches the length parameter
  if (tup->size != (size_t)len) {
    fprintf(
        stderr, "expected tuple size %ld but got size %ld\n", len, tup->size
    );
    exit(EXIT_FAILURE);
  }

  // Return the input tuple since no void type in snake
  return tuple;
}

/// Used by a programmer to exit the program with a specific value
/// \param val A value to print out before exiting the program
void fail(const snakeval_t val) { error(PROGRAMMER_FAIL, val); }

/// Prints an error from the runtime which might be include an unexpected value
/// \param err_code Error code to choose message
/// \param val An optional value that might not have been expected
void error(const int err_code, const snakeval_t val) {
  switch (err_code) {
  case COMP_NOT_NUM:
    fprintf(stderr, "comparison expected a number, got: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case ARITH_NOT_NUM:
    fprintf(stderr, "arithmetic expected a number, got: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case LOGIC_NOT_BOOL:
    fprintf(stderr, "logic expected a boolean, got: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case IF_NOT_BOOL:
    fprintf(stderr, "if expected a boolean, got: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case OVERFLOW:
    fprintf(stderr, "overflow occurred with value: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case ACCESS_NOT_TUPLE:
    fprintf(stderr, "access expected a tuple, got: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case INDEX_NOT_NUM:
    fprintf(stderr, "access expected a number, got: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case ACCESS_LOW_INDEX:
    fprintf(stderr, "index too low to access: ");
    output_snakeval(val | TUPLE_TAG, stderr);
    fprintf(stderr, "\n");
    break;
  case ACCESS_HIGH_INDEX:
    fprintf(stderr, "index too high to access: ");
    output_snakeval(val | TUPLE_TAG, stderr);
    fprintf(stderr, "\n");
    break;
  case NIL_DEREF: fprintf(stderr, "attempt to dereference nil\n"); break;
  case OUT_OF_MEMORY: fprintf(stderr, "out of memory\n"); break;
  case CALL_NOT_CLOSURE:
    fprintf(stderr, "tried to call a non-closure value: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case CALL_ARITY:
    fprintf(stderr, "arity mismatch in call: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case NOT_STRING:
    fprintf(stderr, "operation expected a string, got: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case CLOSURE_TO_STRING:
    fprintf(stderr, "cannot convert closure to string: ");
    output_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case SLICE_LOW_INDEX:
    fprintf(stderr, "index too low to slice: ");
    output_snakeval(val | STRING_TAG, stderr);
    fprintf(stderr, "\n");
    break;
  case SLICE_HIGH_INDEX:
    fprintf(stderr, "index too high to slice: ");
    output_snakeval(val | STRING_TAG, stderr);
    fprintf(stderr, "\n");
    break;
  case STRING_NOT_BOOL:
    fprintf(stderr, "string not representing a boolean: '");
    output_snakeval(val, stderr);
    fprintf(stderr, "'\n");
    break;
  case STRING_NOT_INT:
    fprintf(stderr, "string not representing an integer: '");
    output_snakeval(val, stderr);
    fprintf(stderr, "'\n");
    break;
  case PROGRAMMER_FAIL:
    fprintf(stderr, "user error: '");
    output_snakeval(val, stderr);
    fprintf(stderr, "'\n");
    break;
  default: fprintf(stdout, "Unknown error code: %d", err_code);
  }
  free(heap_alloc_ptr);
  sbt_destroy(&string_map);
  exit(err_code);
}

int main(const int argc, const char* argv[]) {
  const size_t max_heap_size = 100000;
  const int    max_str_size  = 2000;

  heap_size = max_heap_size;
  if (argc > 1 && strcmp("def", argv[1]) != 0 &&
      (sscanf(argv[1], "%zu", &heap_size) != 1 || heap_size > max_heap_size)) {
    fprintf(stderr, "Invalid heap size: %s\n", argv[1]);
    return EXIT_FAILURE;
  }

  int str_size = -1;
  if (argc > 2 && (sscanf(argv[2], "%u", &str_size) != 1 ||
                   str_size > max_str_size || str_size < -1)) {
    fprintf(stderr, "Invalid string map maximum capacity: %s\n", argv[2]);
    return EXIT_FAILURE;
  }

  sbt_initialize(&string_map, str_size >= 0 ? (size_t)str_size : SIZE_MAX);

  heap_alloc_ptr = calloc(heap_size + 15, sizeof(uint64_t));
  heap_base_ptr  = pun_itop((pun_ptoi(heap_alloc_ptr) + 15) & ~0xFUL);
  heap_end_ptr   = heap_base_ptr + heap_size;
  heap_cursor    = heap_base_ptr;

  snakeval_t result = our_code_starts_here();
  print(result);

  free(heap_alloc_ptr);
  sbt_destroy(&string_map);
  return EXIT_SUCCESS;
}

/// Intentionally placing this code below main and all other runtime code so
/// that they will not be able to access these variables and funcctions.

/// Global variable set by our_code_starts_here which marks the bottom of the
/// snake stack
const uint64_t* snake_entry_base_pointer;

/// Print the current stack in the snake language. The two input parameters
/// \c cur_stack_ptr and \c cur_base_ptr must be the value of \c RSP and \c RBP
/// at the point when \c print_stack was called.
///
/// For the purposes of the C object model, we assume that \c cur_stack_ptr and
/// \c cur_base_ptr are pointing to elements of a larger \c uint64_t array.
///
/// CS4410: This must be a Prim1 since there is no way to represent RBP and
/// RSP as immediate expression in our intermediate representation. These two
/// values are implicit inputs that do not show up in the input language and
/// don't need to appear in IR when using Prim1.
///
/// \param pass_through return value for function
/// \param cur_stack_ptr value of \c RSP when called
/// \param cur_base_ptr value of \c RBP when called
/// \return pass_through value
snakeval_t print_stack(
    const snakeval_t      pass_through,
    const uint64_t* const cur_stack_ptr,
    const uint64_t* const cur_base_ptr
) {
  assert(
      sizeof(uint64_t*) == sizeof(uint64_t) && "only 64-bit pointers supported"
  );

  // Print the header information
  printf("RSP: 0x%016lx ==> %ld\n", pun_ptoi(cur_stack_ptr), *cur_stack_ptr);
  printf("RBP: 0x%016lx ==> %ld\n", pun_ptoi(cur_base_ptr), *cur_base_ptr);
  printf(
      "BOT: 0x%016lx ==> %ld\n",
      pun_ptoi(snake_entry_base_pointer),
      *snake_entry_base_pointer
  );

  printf("(difference: %td)\n", cur_stack_ptr - cur_base_ptr);
  printf("Requested return val: 0x%016lx        ==>  ", pass_through);
  output_snakeval(pass_through, stdout);
  printf("\n\nStack Traces:\n");

  const uint64_t* cur_ptr  = cur_stack_ptr;
  const uint64_t* next_rbp = cur_base_ptr;

  enum {
    STATE_END,
    STATE_SNAKEVAL,
    STATE_RBP,
    STATE_RETVAT,
    STATE_BOTTOM_RBP,
    STATE_BOTTOM_RETVAL,
  } loop_state = cur_stack_ptr != cur_base_ptr             ? STATE_SNAKEVAL
               : cur_stack_ptr == snake_entry_base_pointer ? STATE_BOTTOM_RBP
                                                           : STATE_RBP;

  if (loop_state == STATE_RBP) next_rbp = pun_itop(*next_rbp);

  while (loop_state != STATE_END) {
    // Print the prefix for the line
    switch (loop_state) {
    case STATE_END: assert(0); break;
    case STATE_RBP: printf("RBP "); break;
    case STATE_BOTTOM_RBP: printf("BOT "); break;
    case STATE_SNAKEVAL:
    case STATE_RETVAT:
    case STATE_BOTTOM_RETVAL: printf("    "); break;
    }

    // Print the current pointer to the stack and the hex data
    printf("0x%016lx: 0x%016lx      ==>  ", pun_ptoi(cur_ptr), *cur_ptr);

    switch (loop_state) {
    case STATE_END: assert(0); break;
    case STATE_RBP:
    case STATE_BOTTOM_RBP: printf("saved rbp"); break;
    case STATE_SNAKEVAL: output_snakeval(*cur_ptr, stdout); break;
    case STATE_RETVAT:
    case STATE_BOTTOM_RETVAL: printf("saved return address"); break;
    }
    printf("\n");

    cur_ptr += 1;
    switch (loop_state) {
    case STATE_END: assert(0); break;
    case STATE_RBP: loop_state = STATE_RETVAT; break;
    case STATE_RETVAT: loop_state = STATE_SNAKEVAL; break;
    case STATE_BOTTOM_RBP: loop_state = STATE_BOTTOM_RETVAL; break;
    case STATE_BOTTOM_RETVAL: loop_state = STATE_END; break;
    case STATE_SNAKEVAL:
      if (pun_ptoi(cur_ptr) == pun_ptoi(snake_entry_base_pointer)) {
        loop_state = STATE_BOTTOM_RBP;
      } else if (pun_ptoi(cur_ptr) == pun_ptoi(next_rbp)) {
        loop_state = STATE_RBP;
        next_rbp   = pun_itop(*next_rbp);
      }
      break;
    }
  }
  return pass_through;
}
