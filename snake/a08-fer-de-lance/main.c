#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/// Alias for our special encoding of values into 64 bits
typedef uint64_t snakeval_t;

/// Alias for encoding of function addresses use in snake
typedef uint64_t snake_address_t;

/// Runtime type for accessing tuples. This accurately models the data layout of
/// tuples while providing better type safety and interaction than doing pointer
/// arithmetic manually.
typedef struct {
  /// Size is not encoded as a snakeval so size_t makes most sense
  size_t size;
  /// Values are in the struct body but unbound length
  snakeval_t values[];
} snake_tuple_t;

/// Runtime type for accessing functions.
typedef struct {
  /// Arity is not encoded as a snakeval so size_t makes most sense
  size_t arity;
  /// Function address is 64-bits since we depend on x86
  snake_address_t func_addr;
  /// Number of free variables is not encoded as a snakeval so size_t makes most
  /// sense
  size_t free_var_cnt;
  /// Free variables closed over by the closure
  snakeval_t free_vars[];
} snake_closure_t;

/// Error codes for runtime failures
enum error_codes {
  COMP_NOT_NUM      = 1L,
  ARITH_NOT_NUM     = 2L,
  LOGIC_NOT_BOOL    = 3L,
  IF_NOT_BOOL       = 4L,
  OVERFLOW          = 5L,
  ACCESS_NOT_TUPLE  = 6L,
  INDEX_NOT_NUM     = 7L,
  ACCESS_LOW_INDEX  = 8L,
  ACCESS_HIGH_INDEX = 9L,
  NIL_DEREF         = 10L,
  OUT_OF_MEMORY     = 11L,
  CALL_NOT_CLOSURE  = 12L,
  CALL_ARITY        = 13L,
};

/// snakeval_t sub types
typedef enum {
  SV_INVALID,
  SV_PADDING,
  SV_BOOL,
  SV_NUM,
  SV_TUPLE,
  SV_CLOSURE,
} snakeval_type_t;

/// Exported function declarations
extern snakeval_t our_code_starts_here(uint64_t* h) asm("our_code_starts_here");
extern snakeval_t print(snakeval_t val) asm("print");
extern snakeval_t input(void) asm("input");
extern snakeval_t equal(snakeval_t lhs, snakeval_t rhs) asm("equal");
extern void       error(int errCode, snakeval_t val) asm("error");
extern void       set_stack_bottom(const uint64_t* sb) asm("set_stack_bottom");
extern snakeval_t print_stack(
    snakeval_t      pass_through,
    const uint64_t* cur_stack_ptr,
    const uint64_t* cur_base_ptr
) asm("print_stack");
extern snakeval_t
assert_tuple_len(snakeval_t tuple, snakeval_t len) asm("assert_tuple_len");
extern snakeval_t print_raw(snakeval_t val) asm("print_raw$");

/// Exported variable declarations
extern const uint64_t* snake_entry_base_pointer asm("snake_entry_base_pointer");
extern uint64_t*       heap_base_ptr asm("heap_base_ptr");
extern uint64_t*       heap_end_ptr asm("heap_end_ptr");
extern size_t          heap_size asm("heap_size");
extern uint64_t*       snake_heap_reg_save asm("snake_heap_reg_save");

/// Magic number used as a padding value on the stack and heap. This value would
/// be interpreted as a bool by snake but the snake assembly should never read
/// it. The value ensures that stack and heap printing will ignore the useless
/// stack location.
static const uint64_t PADDING_VALUE = 0xffffffffdeadbeefL;

/// Masks to reveal the prefix bits of a snakeval
static const uint64_t BOOL_TAG_MASK    = 0x0000000000000007L;
static const uint64_t NUM_TAG_MASK     = 0x0000000000000001L;
static const uint64_t TUPLE_TAG_MASK   = 0x0000000000000007L;
static const uint64_t CLOSURE_TAG_MASK = 0x0000000000000007L;

/// Tag prefixes of specific type encodings
static const uint64_t BOOL_TAG    = 0x0000000000000007L;
static const uint64_t NUM_TAG     = 0x0000000000000000L;
static const uint64_t TUPLE_TAG   = 0x0000000000000001L;
static const uint64_t CLOSURE_TAG = 0x0000000000000005L;

/// Macro predicates to determine snake value type
#define SV_IS_TYPE(_val_, _type_)                                              \
  (((_val_) & (_type_##_TAG_MASK)) == _type_##_TAG)
#define SV_IS_BOOL(_val_)    SV_IS_TYPE(_val_, BOOL)
#define SV_IS_NUM(_val_)     SV_IS_TYPE(_val_, NUM)
#define SV_IS_TUPLE(_val_)   SV_IS_TYPE(_val_, TUPLE)
#define SV_IS_CLOSURE(_val_) SV_IS_TYPE(_val_, CLOSURE)

/// Functions for punning ints to pointers and reverse
uint64_t pun_ptoi(const uint64_t* const ptr) {
  uint64_t val;
  memcpy(&val, &ptr, sizeof(val));
  return val;
}
uint64_t* pun_itop(const uint64_t val) {
  uint64_t* ptr;
  memcpy(&ptr, &val, sizeof(ptr));
  return ptr;
}

/// Constants for some of the actual snake values
static const snakeval_t BOOL_TRUE  = 0xFFFFFFFFFFFFFFFFL;
static const snakeval_t BOOL_FALSE = 0x7FFFFFFFFFFFFFFFL;
static const snakeval_t TUPLE_NIL  = TUPLE_TAG;

/// Global variables relating to heap accessible to both C runtime and Snake
/// runtime
uint64_t* heap_base_ptr;
uint64_t* heap_end_ptr;
size_t    heap_size;

snakeval_type_t sv_type_of(const snakeval_t val) {
  if (val == PADDING_VALUE) return SV_PADDING;
  if (SV_IS_NUM(val)) return SV_NUM;
  if (SV_IS_BOOL(val)) return SV_BOOL;
  if (SV_IS_TUPLE(val)) return SV_TUPLE;
  if (SV_IS_CLOSURE(val)) return SV_CLOSURE;
  return SV_INVALID;
}

bool sv_to_bool(const snakeval_t val) {
  assert(val == BOOL_FALSE || val == BOOL_TRUE);
  return val == BOOL_TRUE;
}

int64_t sv_to_int(const snakeval_t val) {
  assert(SV_IS_NUM(val));
  // shift bits right to remove tag
  return ((int64_t)val) / 2;
}

snakeval_t bool_to_sv(const bool val) { return val ? BOOL_TRUE : BOOL_FALSE; }
snakeval_t int_to_sv(const int64_t val) {
  if (val >= ((int64_t)1 << 62) || val < -((int64_t)1 << 62)) {
    fprintf(stderr, "Integer input is out of range: %ld\n", val);
    exit(EXIT_FAILURE);
  }
  return (snakeval_t)(val * 2);
}

snake_tuple_t* sv_to_tuple(const snakeval_t val) {
  assert(
      SV_IS_TUPLE(val) && val != TUPLE_NIL &&
      "input to sv_to_tuple must be a non-nil tuple snake value"
  );
  uint64_t untagged = val & ~TUPLE_TAG_MASK;
  assert(
      untagged >= pun_ptoi(heap_base_ptr) &&
      untagged <= pun_ptoi(heap_end_ptr) &&
      "expecting tuple to reside inside heap"
  );
  snake_tuple_t* ptr;
  memcpy(&ptr, &untagged, sizeof(ptr));
  return ptr;
}

snake_closure_t* sv_to_closure(const snakeval_t val) {
  assert(
      SV_IS_CLOSURE(val) &&
      "input to sv_to_closure must be a closure snake value"
  );
  uint64_t untagged = val & ~CLOSURE_TAG_MASK;
  assert(
      untagged >= pun_ptoi(heap_base_ptr) &&
      untagged <= pun_ptoi(heap_end_ptr) &&
      "expecting closure to reside inside heap"
  );
  snake_closure_t* ptr;
  memcpy(&ptr, &untagged, sizeof(ptr));
  return ptr;
}

snakeval_t print_raw(snakeval_t val) {
  printf("0x%016lx ==> %ld\n", val, val);
  return val;
}

/// Prints a snake value to the given output stream
///
/// \param val Snake value to print out
/// \param stream Output stream to print the result
/// \return count of charaters printed to stream
static int output_snakeval(const snakeval_t val, FILE* const stream) {
  switch (sv_type_of(val)) {
  case SV_INVALID: return fprintf(stream, "Unknown value: 0x%016lx", val);
  case SV_PADDING: return fprintf(stream, "<padding value>");
  case SV_BOOL:
    return fprintf(stream, "%s", sv_to_bool(val) ? "true" : "false");
  case SV_NUM: return fprintf(stream, "%ld", sv_to_int(val));
  case SV_CLOSURE: {
    const snake_closure_t* const closure = sv_to_closure(val);
    return fprintf(
        stream,
        "<closure, arity = %ld, free_var_cnt = %ld>",
        closure->arity,
        closure->free_var_cnt
    );
  }
  case SV_TUPLE: {
    /// Handle nil tuple
    if (val == TUPLE_NIL) return fprintf(stream, "nil");

    snake_tuple_t* const tuple = sv_to_tuple(val);
    const size_t         size  = tuple->size;

    const size_t seen_tag = 0xffffffffffffffff;

    if (tuple->size == seen_tag) return fprintf(stream, "<cyclic tuple>");

    // Save the length and tag the tuple as seen
    const size_t len = tuple->size;
    tuple->size      = seen_tag;

    // Sum all calls to stream output to preserve semantics
    int output_sum = 0;
    output_sum += fprintf(stream, "(");

    // Loop over each value in the tuple and recursively print
    for (size_t i = 0; i < len; ++i) {
      if (i > 0) output_sum += fprintf(stream, ", ");
      output_sum += output_snakeval(tuple->values[i], stream);
    }

    // Print final paren and handle single element tuple comma
    output_sum += fprintf(stream, size == 1 ? ",)" : ")");

    // Restore the actual length
    tuple->size = len;

    return output_sum;
  }
  }
  assert(false); // Should be unreachable
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
  assert(type != SV_INVALID && type != SV_PADDING);

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

/// Reads in user data from stdin. Attempts to parse it as a snake number or
/// boolean. Exits the program if any exceptions occur.
///
/// This looks at the next non-whitespace containing string for each input. As
/// such, if multiple inputs are entered on the same line, the remaining inputs
/// will be used in the next call to input.
///
/// \exception
/// - No input left leading to EOF on scan attempt
/// - Input is so long that it would fill whole buffer
/// - Parsing an integer would range overflow 64 bits
/// - Parsed integer does not fit snake value constraint
/// - Input in the buffer is neither boolean nor integer
///
/// \return Successfully parsed snake number or boolean
snakeval_t input(void) {
  // Buffer is large enough to always fit a valid 64-bit integer decimal string
  // Make sure to zero initialize
  char buf[32] = {0};

  // Tag last entry in the buffer to check if input is too long
  buf[31] = '@';

  {
    // Scan non-whitespace string as user input into the buffer
    int rv = scanf("%31s", buf);
    // If EOF then we ran out of input
    if (rv == EOF) {
      fprintf(stderr, "Ran out of input: EOF");
      exit(EXIT_FAILURE);
    }
    // If not 1 or tag replaced with null terminator, then input fails
    if (rv != 1 || buf[31] != '@') {
      fprintf(stderr, "Input does not fit into buffer");
      exit(EXIT_FAILURE);
    }
  }

  {
    int64_t val = 0;
    // Try parsing an integer
    if (sscanf(buf, "%ld", &val) == 1) {
      // Check errno in case the value is too big
      if (errno != 0) {
        perror("Input failed");
        exit(EXIT_FAILURE);
      }
      // Convert integer to snake value and return
      return int_to_sv(val);
    }
  }

  // Compare input against boolean strings
  if (strcmp("true", buf) == 0) return bool_to_sv(true);
  if (strcmp("false", buf) == 0) return bool_to_sv(false);

  // All cases failed so we have an unknown input
  fprintf(stderr, "Unknown input: %s\n", buf);
  exit(EXIT_FAILURE);
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
  default: fprintf(stdout, "Unknown error code: %d", err_code);
  }
  free(heap_base_ptr);
  exit(err_code);
}

int main(const int argc, const char* argv[]) {
  const size_t max_heap_size = 50000;
  heap_size                  = max_heap_size;
  if (argc > 1 && sscanf(argv[1], "%zu", &heap_size) != 1 &&
      heap_size > max_heap_size) {
    fprintf(stderr, "Invalid heap size: %s\n", argv[1]);
    return EXIT_FAILURE;
  }

  heap_base_ptr = calloc(heap_size, sizeof(uint64_t));
  heap_end_ptr  = heap_base_ptr + heap_size;

  snakeval_t result = our_code_starts_here(heap_base_ptr);
  print(result);

  free(heap_base_ptr);
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

/// Intentionally placed at bottom of file so that C code does not touch.
uint64_t* snake_heap_reg_save;
