#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/// Alias for our special encoding of values into 64 bits
typedef uint64_t snakeval_t;

/// Error codes for runtime failures
enum error_codes {
  COMP_NOT_NUM   = 1L,
  ARITH_NOT_NUM  = 2L,
  LOGIC_NOT_BOOL = 3L,
  IF_NOT_BOOL    = 4L,
  OVERFLOW       = 5L
};

/// Exported function declarations
extern snakeval_t our_code_starts_here(void) asm("our_code_starts_here");
extern snakeval_t print(snakeval_t val) asm("print");
extern void       error(int errCode, snakeval_t val) asm("error");
extern void       set_stack_bottom(const uint64_t* sb) asm("set_stack_bottom");
extern snakeval_t print_stack(
    snakeval_t      pass_through,
    const uint64_t* cur_stack_ptr,
    const uint64_t* cur_base_ptr
) asm("print_stack");

/// Masks to reveal the prefix bits of a snakeval
static const uint64_t BOOL_TAG_MASK = 0x0000000000000007L;
static const uint64_t NUM_TAG_MASK  = 0x0000000000000001L;

/// Tag prefixes of specific type encodings
static const uint64_t BOOL_TAG = 0x0000000000000007L;
static const uint64_t NUM_TAG  = 0x0000000000000000L;

/// Macro predicates to determine snake value type
#define SV_IS_TYPE(_val_, _type_)                                              \
  (((_val_) & (_type_##_TAG_MASK)) == _type_##_TAG)
#define SV_IS_NUM(_val_)  SV_IS_TYPE(_val_, NUM)
#define SV_IS_BOOL(_val_) SV_IS_TYPE(_val_, BOOL)

/// Constants for some of the actual snake values
static const snakeval_t BOOL_TRUE = 0xFFFFFFFFFFFFFFFFL;

bool sv_to_bool(const snakeval_t val) {
  assert(SV_IS_BOOL(val));
  return val == BOOL_TRUE;
}

int64_t sv_to_int(const snakeval_t val) {
  assert(SV_IS_NUM(val));
  // shift bits right to remove tag
  return ((int64_t)val) / 2;
}

/// Prints a snake value to the given output stream
/// \param val Snake value to print out
/// \param stream Output stream to print the result
static int output_snakeval(const snakeval_t val, FILE* const stream) {
  // Handle boolean values
  if (SV_IS_BOOL(val))
    return fprintf(stream, "%s", sv_to_bool(val) ? "true" : "false");

  // Handle integer values
  if (SV_IS_NUM(val)) return fprintf(stream, "%ld", sv_to_int(val));

  // print unknown val in hex as fall through
  return fprintf(stream, "Unknown value: %#018lx", val);
}

/// Prints the value to stdout then returns the same value actings as an
/// identity function
/// \param val Snake value to print and return
/// \return Value passed in
snakeval_t print(const snakeval_t val) {
  output_snakeval(val, stdout);
  printf("\n");
  return val;
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
  default: fprintf(stdout, "Unknown error code: %d", err_code);
  }
  exit(err_code);
}

int main(void) {
  snakeval_t result = our_code_starts_here();
  print(result);
  return 0;
}

/// Intentionally placing this code below main and all other runtime code so
/// that they will not be able to access these variables and funcctions.

/// Global variable set by our_code_starts_here which marks the bottom of the
/// snake stack
static const uint64_t* snake_entry_base_pointer;

void set_stack_bottom(const uint64_t* const sb) {
  snake_entry_base_pointer = sb;
}

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

#define PUN_PTOI(_ptr_) (*(uint64_t*)&(_ptr_))
#define PUN_ITOP(_int_) (*(uint64_t**)&(_int_))

  // Print the header information
  printf("RSP: 0x%016lx ==> %ld\n", PUN_PTOI(cur_stack_ptr), *cur_stack_ptr);
  printf("RBP: 0x%016lx ==> %ld\n", PUN_PTOI(cur_base_ptr), *cur_base_ptr);
  printf(
      "BOT: 0x%016lx ==> %ld\n",
      PUN_PTOI(snake_entry_base_pointer),
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

  if (loop_state == STATE_RBP) next_rbp = PUN_ITOP(*next_rbp);

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
    printf("0x%016lx: 0x%016lx      ==>  ", PUN_PTOI(cur_ptr), *cur_ptr);

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
      if (PUN_PTOI(cur_ptr) == PUN_PTOI(snake_entry_base_pointer)) {
        loop_state = STATE_BOTTOM_RBP;
      } else if (PUN_PTOI(cur_ptr) == PUN_PTOI(next_rbp)) {
        loop_state = STATE_RBP;
        next_rbp   = PUN_ITOP(*next_rbp);
      }
      break;
    }
  }
  return pass_through;
}
#undef PUN_ITOP
#undef PUN_PTOI
