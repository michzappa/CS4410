#ifndef STRING_SPAN_H
#define STRING_SPAN_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/// String representation used for managing the memory during runtime. Contains
/// the pointer to memory and the length of the buffer. Snake values at runtime
/// might be pointing at any point in the memory buffer as a view of the data.
typedef struct string_span {
  const char* string;
  size_t      length;
} string_span_t;

/// Information used in the garbage collector for strings
typedef struct str_metadata {
  uint8_t visit_idx;
} str_metadata_t;

void string_span_destroy(string_span_t str);

int  string_span_cmp(string_span_t lhs, string_span_t rhs);
bool string_span_contain(string_span_t str, const char* sub_str);

#ifdef __cplusplus
}
#endif

#endif // STRING_SPAN_H
