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
extern snakeval_t our_code_starts_here() asm("our_code_starts_here");
extern snakeval_t print(snakeval_t val) asm("print");
extern void       error(int errCode, snakeval_t val) asm("error");

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
static const snakeval_t BOOL_TRUE  = 0xFFFFFFFFFFFFFFFFL;
static const snakeval_t BOOL_FALSE = 0x7FFFFFFFFFFFFFFFL;

/// Prints a snake value to the given output stream
/// \param val Snake value to print out
/// \param stream Output stream to print the result
static void fprint_snakeval(const snakeval_t val, FILE* stream) {
  // Handle all constant values
  switch (val) {
  case BOOL_TRUE: return (void)fprintf(stream, "true");
  case BOOL_FALSE: return (void)fprintf(stream, "false");
  default: break;
  }

  // Handle integer values
  if (SV_IS_NUM(val)) {
    // shift bits right to remove tag
    int64_t actual = ((int64_t)val) / 2;
    fprintf(stream, "%ld", actual);
    return;
  }

  // print unknown val in hex as fall through
  fprintf(stream, "Unknown value: %#018lx", val);
}

/// Prints the value to stdout then returns the same value actings as an
/// identity function
/// \param val Snake value to print and return
/// \return Value passed in
snakeval_t print(const snakeval_t val) {
  fprint_snakeval(val, stdout);
  printf("\n");
  return val;
}

/// Prints an error from the runtime which might be include an unexpected value
/// \param err_code Error code to choose message
/// \param val An optional value that might not have been expected
void error(int err_code, snakeval_t val) {
  switch (err_code) {
  case COMP_NOT_NUM:
    fprintf(stderr, "comparison expected a number, got: ");
    fprint_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case ARITH_NOT_NUM:
    fprintf(stderr, "arithmetic expected a number, got: ");
    fprint_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case LOGIC_NOT_BOOL:
    fprintf(stderr, "logic expected a boolean, got: ");
    fprint_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case IF_NOT_BOOL:
    fprintf(stderr, "if expected a boolean, got: ");
    fprint_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  case OVERFLOW:
    fprintf(stderr, "overflow occurred with value: ");
    fprint_snakeval(val, stderr);
    fprintf(stderr, "\n");
    break;
  default: fprintf(stdout, "Unknown error code: %d", err_code);
  }
  exit(err_code);
}

int main(const int argc, const char* argv[]) {
  snakeval_t result = our_code_starts_here();
  print(result);
  return 0;
}
