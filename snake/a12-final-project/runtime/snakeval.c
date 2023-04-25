#include "snakeval.h"

#include <assert.h>

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

snakeval_type_t sv_type_of(const snakeval_t val) {
  if (val == PADDING_VALUE) return SV_PADDING;
  if (SV_IS_NUM(val)) return SV_NUM;
  if (SV_IS_BOOL(val) && (val == BOOL_FALSE || val == BOOL_TRUE))
    return SV_BOOL;
  if (SV_IS_TUPLE(val)) return SV_TUPLE;
  if (SV_IS_CLOSURE(val)) return SV_CLOSURE;
  if (SV_IS_STRING(val)) return SV_STRING;
  return SV_INVALID;
}

bool sv_to_bool(const snakeval_t val) {
  assert(val == BOOL_FALSE || val == BOOL_TRUE);
  return val == BOOL_TRUE;
}
snakeval_t bool_to_sv(const bool val) { return val ? BOOL_TRUE : BOOL_FALSE; }

int64_t sv_to_int(const snakeval_t val) {
  assert(SV_IS_NUM(val));
  // shift bits right to remove tag
  return ((int64_t)val) / 2;
}
snakeval_t int_to_sv(const int64_t val) {
  if (val >= ((int64_t)1 << 62) || val < -((int64_t)1 << 62)) {
    fprintf(stderr, "Integer input is out of range: %ld\n", val);
    exit(EXIT_FAILURE);
  }
  return (snakeval_t)(val * 2);
}

snake_tuple_t* sv_to_tuple_unchecked(const snakeval_t val) {
  uint64_t       untagged = val & ~TUPLE_TAG_MASK;
  snake_tuple_t* ptr;
  memcpy(&ptr, &untagged, sizeof(ptr));
  return ptr;
}
snake_tuple_t* sv_to_tuple(const snakeval_t val) {
  assert(
      SV_IS_TUPLE(val) && val != TUPLE_NIL &&
      "input to sv_to_tuple must be a non-nil tuple snake value"
  );
  return sv_to_tuple_unchecked(val);
}

snake_closure_t* sv_to_closure_unchecked(const snakeval_t val) {
  uint64_t         untagged = val & ~CLOSURE_TAG_MASK;
  snake_closure_t* ptr;
  memcpy(&ptr, &untagged, sizeof(ptr));
  return ptr;
}
snake_closure_t* sv_to_closure(const snakeval_t val) {
  assert(
      SV_IS_CLOSURE(val) &&
      "input to sv_to_closure must be a closure snake value"
  );
  return sv_to_closure_unchecked(val);
}

snake_string_t* sv_to_string_unchecked(const snakeval_t val) {
  uint64_t        untagged = val & ~STRING_TAG_MASK;
  snake_string_t* ptr;
  memcpy(&ptr, &untagged, sizeof(ptr));
  return ptr;
}
snake_string_t* sv_to_string(const snakeval_t val) {
  assert(
      SV_IS_STRING(val) && "input to sv_to_string must be a string snake value"
  );
  return sv_to_string_unchecked(val);
}

/// Prints a snake value to the given output stream
///
/// \param val Snake value to print out
/// \param stream Output stream to print the result
/// \return count of charaters printed to stream
int output_snakeval(const snakeval_t val, FILE* const stream) {
  switch (sv_type_of(val)) {
  case SV_INVALID: return fprintf(stream, "Unknown value: 0x%016lx", val);
  case SV_PADDING: return fprintf(stream, "<padding value>");
  case SV_FWD_PTR: return fprintf(stream, "<forwarding pointer>");
  case SV_BOOL:
    return fprintf(stream, "%s", sv_to_bool(val) ? "true" : "false");
  case SV_NUM: return fprintf(stream, "%ld", sv_to_int(val));
  case SV_CLOSURE: {
    snake_closure_t* const closure    = sv_to_closure(val);
    int                    output_sum = fprintf(
        stream,
        "<closure, arity = %ld, free_var_cnt = %ld, ",
        closure->arity,
        closure->free_var_cnt
    );

    // Lambdas with zero free vars are likely in read only memory
    if (closure->free_var_cnt == 0) return fprintf(stream, "[]>");

    const size_t seen_tag = 0xffffffffffffffff;

    if (closure->free_var_cnt == seen_tag)
      return fprintf(stream, "<cyclic closure>");

    // Save the length and tag the closure as seen
    const size_t len      = closure->free_var_cnt;
    closure->free_var_cnt = seen_tag;

    // Sum all calls to stream output to preserve semantics
    output_sum += fprintf(stream, "[");

    // Loop over each free var in the closure and recursively print
    for (size_t i = 0; i < len; ++i) {
      if (i > 0) output_sum += fprintf(stream, ", ");
      output_sum += output_snakeval(closure->free_vars[i], stream);
    }

    // Print final bracket and handle single free var closure comma
    output_sum += fprintf(stream, "]>");

    // Restore the actual length
    closure->free_var_cnt = len;

    return output_sum;
  }
  case SV_TUPLE: {
    /// Handle nil tuple
    if (val == TUPLE_NIL) return fprintf(stream, "nil");

    snake_tuple_t* const tuple = sv_to_tuple(val);
    const size_t         size  = tuple->size;

    // If the size is zero then it is in read only memory likely
    if (tuple->size == 0) return fprintf(stream, "()");

    const size_t seen_tag = 0xffffffffffffffff;

    if (tuple->size == seen_tag) return fprintf(stream, "<cyclic tuple>");

    // Save the length and tag the tuple as seen
    const size_t len = tuple->size;
    tuple->size      = seen_tag;

    // Sum all calls to stream output to preserve semantics
    int output_sum = fprintf(stream, "(");

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
  case SV_STRING: {
    snake_string_t* const string    = sv_to_string(val);
    const int             length    = (int)string->length;
    const char*           str_bytes = string->string;

    return fprintf(stream, "%.*s", length, str_bytes);
  }
  }
  assert(false); // Should be unreachable
}
