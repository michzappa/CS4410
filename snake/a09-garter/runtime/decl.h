#include <stdint.h>
#include <stdlib.h>

/// Alias for our special encoding of values into 64 bits
typedef uint64_t snakeval_t;

/// Exported variable declarations
extern const uint64_t* snake_entry_base_pointer asm("snake_entry_base_pointer");
extern uint64_t*       snake_heap_reg_save asm("snake_heap_reg_save");

/// C visible global variables for the heap
extern uint64_t* heap_alloc_ptr;
extern uint64_t* heap_base_ptr;
extern uint64_t* heap_end_ptr;
extern size_t    heap_size;

/// Exported function declarations
extern snakeval_t our_code_starts_here(uint64_t* heap_ptr) asm("our_code_starts_here");

extern snakeval_t print(snakeval_t val) asm("print");
extern snakeval_t input(void) asm("input");
extern snakeval_t equal(snakeval_t lhs, snakeval_t rhs) asm("equal");

extern void error(int errCode, snakeval_t val) asm("error");
extern snakeval_t
assert_tuple_len(snakeval_t tuple, snakeval_t len) asm("assert_tuple_len");

extern snakeval_t print_stack(
    snakeval_t      pass_through,
    const uint64_t* cur_stack_ptr,
    const uint64_t* cur_base_ptr
) asm("print_stack");

extern snakeval_t print_raw(snakeval_t val) asm("print_raw");

extern uint64_t* try_gc(
    uint64_t* alloc_ptr,
    uint64_t  amount_needed,
    uint64_t* first_frame,
    uint64_t* stack_top
) asm("try_gc");

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
