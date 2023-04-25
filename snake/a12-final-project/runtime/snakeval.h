#ifndef SNAKEVAL_H
#define SNAKEVAL_H

#include "decl.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

typedef struct {
  size_t      length;
  const char* string;
} snake_string_t;

/// snakeval_t sub types
typedef enum {
  SV_INVALID,
  SV_PADDING,
  SV_BOOL,
  SV_NUM,
  SV_TUPLE,
  SV_CLOSURE,
  SV_FWD_PTR,
  SV_STRING,
} snakeval_type_t;

/// Magic number used as a padding value on the stack and heap. This value would
/// be interpreted as a bool by snake but the snake assembly should never read
/// it. The value ensures that stack and heap printing will ignore the useless
/// stack location.
#define PADDING_VALUE 0xffffffffdeadbeefUL

/// Masks to reveal the prefix bits of a snakeval
#define BOOL_TAG_MASK    0x000000000000000FUL
#define NUM_TAG_MASK     0x0000000000000001UL
#define TUPLE_TAG_MASK   0x000000000000000FUL
#define CLOSURE_TAG_MASK 0x000000000000000FUL
#define FWD_PTR_TAG_MASK 0x000000000000000FUL
#define STRING_TAG_MASK  0x000000000000000FUL

/// Tag prefixes of specific type encodings
#define BOOL_TAG    0x000000000000000FUL
#define NUM_TAG     0x0000000000000000UL
#define TUPLE_TAG   0x0000000000000001UL
#define CLOSURE_TAG 0x0000000000000005UL
#define FWD_PTR_TAG 0x0000000000000003UL
#define STRING_TAG  0x000000000000000BUL

/// Constants for some of the actual snake values
#define BOOL_TRUE  0xFFFFFFFFFFFFFFFFUL
#define BOOL_FALSE 0x7FFFFFFFFFFFFFFFUL
#define TUPLE_NIL  0x0000000000000001UL

/// Macro predicates to determine snake value type
#define SV_IS_TYPE(_val_, _type_)                                              \
  (((_val_) & (_type_##_TAG_MASK)) == _type_##_TAG)
#define SV_IS_BOOL(_val_)    SV_IS_TYPE(_val_, BOOL)
#define SV_IS_NUM(_val_)     SV_IS_TYPE(_val_, NUM)
#define SV_IS_TUPLE(_val_)   SV_IS_TYPE(_val_, TUPLE)
#define SV_IS_CLOSURE(_val_) SV_IS_TYPE(_val_, CLOSURE)
#define SV_IS_FWD_PTR(_val_) SV_IS_TYPE(_val_, FWD_PTR)
#define SV_IS_STRING(_val_)  SV_IS_TYPE(_val_, STRING)

uint64_t  pun_ptoi(const uint64_t* const ptr);
uint64_t* pun_itop(const uint64_t val);

snakeval_type_t sv_type_of(const snakeval_t val);

bool       sv_to_bool(const snakeval_t val);
snakeval_t bool_to_sv(const bool val);

int64_t    sv_to_int(const snakeval_t val);
snakeval_t int_to_sv(const int64_t val);

snake_tuple_t* sv_to_tuple_unchecked(const snakeval_t val);
snake_tuple_t* sv_to_tuple(const snakeval_t val);

snake_closure_t* sv_to_closure_unchecked(const snakeval_t val);
snake_closure_t* sv_to_closure(const snakeval_t val);

snake_string_t* sv_to_string_unchecked(const snakeval_t val);
snake_string_t* sv_to_string(const snakeval_t val);

int output_snakeval(const snakeval_t val, FILE* const stream);

#endif // SNAKEVAL_H
