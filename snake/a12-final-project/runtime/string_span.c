#include "string_span.h"

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/// Frees the string data being pointed to by the span
void string_span_destroy(string_span_t str) { free((void*)str.string); }

static uintptr_t pun_ccptoi(const char* const ptr) {
  uintptr_t val;
  memcpy(&val, &ptr, sizeof(val));
  return val;
}

/// Compares the unique pointer address of two string spans. Equality is shown
/// by zero. Less than is a negative number. Greater than is a positive number.
/// This is influenced by \c memcmp semantics
/// \return positive number if lhs > rhs, negative if lhs < rhs, otherwise zero
int string_span_cmp(const string_span_t lhs, const string_span_t rhs) {
  ptrdiff_t val = lhs.string - rhs.string;
  return val < 0 ? -1 : val > 0 ? 1 : 0;
}

/// Checks if the string pointer is pointing to data in the string span.
/// Effectively checks if the pointer is contained in the range of the span.
/// \param str span that might contain the sub string
/// \param sub_str string pointer that might point within the span
/// \return true iff the pointer exists in the span
bool string_span_contain(const string_span_t str, const char* const sub_str) {
  return pun_ccptoi(str.string) <= pun_ccptoi(sub_str) &&
         pun_ccptoi(str.string + str.length) > pun_ccptoi(sub_str);
}
