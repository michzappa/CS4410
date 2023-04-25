#include "decl.h"
#include "snakeval.h"

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>

typedef struct str_buf {
  char*  buf;
  size_t length;
  size_t capacity;
} str_buf_t;

#define STR_BUF_INIT                                                           \
  { .buf = NULL, .length = 0, .capacity = 0 }

static void buf_grow(str_buf_t* sb, size_t added_cap) {
  assert(sb != NULL);
  assert(sb->length <= sb->capacity);

  size_t new_cap = sb->capacity + added_cap;
  char*  new_buf = calloc(new_cap, sizeof(char));
  assert(new_buf != NULL);

  if (sb->buf == NULL) {
    assert(sb->length == 0 && sb->capacity == 0);
  } else {
    memcpy(new_buf, sb->buf, sb->length);
  }

  free(sb->buf);
  sb->buf      = new_buf;
  sb->capacity = new_cap;
}

/// Reserves enough bytes at end of buffer
static void buf_reserve(str_buf_t* sb, size_t needed_space) {
  assert(sb != NULL);
  assert(sb->length <= sb->capacity);

  const size_t new_len = sb->length + needed_space;
  if (new_len > sb->capacity) {
    const size_t double_len = sb->length;
    const size_t min_grow   = new_len < double_len ? double_len : new_len;
    buf_grow(sb, min_grow);
  }
}

static char* buf_tail(str_buf_t* sb) {
  assert(sb != NULL);
  assert(sb->length <= sb->capacity);
  return sb->buf + sb->length;
}

static void buf_push_char(str_buf_t* sb, char c) {
  assert(sb != NULL);
  buf_reserve(sb, 1);
  buf_tail(sb)[0] = c;
  sb->length += 1;
}

/// Creates string and over allocates a bit to ensure null character and enough
/// space
void create_string(str_buf_t* sb, snakeval_t val) {
  switch (sv_type_of(val)) {
  case SV_INVALID:
  case SV_PADDING:
  case SV_FWD_PTR: assert(false);
  case SV_CLOSURE: {
    free(sb->buf);
    error(CLOSURE_TO_STRING, val);
  }
  case SV_STRING: {
    const snake_string_t* const string = sv_to_string(val);
    buf_reserve(sb, string->length);
    memcpy(buf_tail(sb), string->string, string->length);
    sb->length += string->length;
    return;
  }
  case SV_BOOL: {
    const bool b = sv_to_bool(val);
    buf_reserve(sb, 6);
    sb->length += (size_t)sprintf(buf_tail(sb), b ? "true" : "false");
    return;
  }
  case SV_NUM: {
    const int64_t v = sv_to_int(val);
    buf_reserve(sb, 22);
    sb->length += (size_t)sprintf(buf_tail(sb), "%ld", v);
    return;
  }
  case SV_TUPLE: {
    /// Handle nil tuple
    if (val == TUPLE_NIL) {
      buf_reserve(sb, 4);
      sb->length += (size_t)sprintf(buf_tail(sb), "nil");
      return;
    }

    snake_tuple_t* const tuple = sv_to_tuple(val);
    const size_t         size  = tuple->size;

    // If the size is zero then it is in read only memory likely
    if (tuple->size == 0) {
      buf_reserve(sb, 3);
      sb->length += (size_t)sprintf(buf_tail(sb), "()");
      return;
    }

    const size_t seen_tag = 0xffffffffffffffff;

    if (tuple->size == seen_tag) {
      buf_reserve(sb, 16);
      sb->length += (size_t)sprintf(buf_tail(sb), "<cyclic tuple>");
      return;
    }

    // Save the length and tag the tuple as seen
    const size_t len = tuple->size;
    tuple->size      = seen_tag;

    // Sum all calls to stream output to preserve semantics
    buf_reserve(sb, 2);
    sb->length += (size_t)sprintf(buf_tail(sb), "(");

    // Loop over each value in the tuple and recursively print
    for (size_t i = 0; i < len; ++i) {
      if (i > 0) {
        buf_reserve(sb, 3);
        sb->length += (size_t)sprintf(buf_tail(sb), ", ");
      }
      create_string(sb, tuple->values[i]);
    }

    // Print final paren and handle single element tuple comma
    buf_reserve(sb, 3);
    sb->length += (size_t)sprintf(buf_tail(sb), size == 1 ? ",)" : ")");

    // Restore the actual length
    tuple->size = len;
    return;
  }
  }
  assert(false);
}

snakeval_t to_string(
    snakeval_t val, uint64_t* const cur_stack_ptr, uint64_t* const cur_base_ptr
) {
  if (SV_IS_STRING(val)) return val;

  str_buf_t sb = STR_BUF_INIT;
  create_string(&sb, val);

  uint64_t*       alloc_ptr = reserve_str_gc(cur_base_ptr, cur_stack_ptr);
  snake_string_t* str       = (snake_string_t*)alloc_ptr;
  str->length               = sb.length;
  str->string               = sb.buf;

  string_span_t  span = {.string = sb.buf, .length = sb.length};
  str_metadata_t md   = {.visit_idx = 0};

  bool inserted = sbt_insert(&string_map, span, md);
  assert(inserted);
  (void)inserted;

  return pun_ptoi(alloc_ptr) | STRING_TAG;
}

snakeval_t str_concat(
    snakeval_t      str1,
    snakeval_t      str2,
    uint64_t* const cur_stack_ptr,
    uint64_t* const cur_base_ptr
) {
  if (!SV_IS_STRING(str1)) error(NOT_STRING, str1);
  if (!SV_IS_STRING(str2)) error(NOT_STRING, str2);

  snake_string_t* ss1 = sv_to_string(str1);
  snake_string_t* ss2 = sv_to_string(str2);

  size_t concat_length = ss1->length + ss2->length;

  char* str_buf = calloc(concat_length, sizeof(char));
  assert(str_buf != NULL);
  memcpy(str_buf, ss1->string, ss1->length);
  memcpy(str_buf + ss1->length, ss2->string, ss2->length);

  uint64_t*       alloc_ptr = reserve_str_gc(cur_base_ptr, cur_stack_ptr);
  snake_string_t* str       = (snake_string_t*)alloc_ptr;
  str->length               = concat_length;
  str->string               = str_buf;

  string_span_t  span = {.string = str_buf, .length = concat_length};
  str_metadata_t md   = {.visit_idx = 0};

  bool inserted = sbt_insert(&string_map, span, md);
  assert(inserted);
  (void)inserted;

  return pun_ptoi(alloc_ptr) | STRING_TAG;
}

snakeval_t str_slice(
    snakeval_t      str1,
    snakeval_t      low,
    snakeval_t      high,
    uint64_t* const cur_stack_ptr,
    uint64_t* const cur_base_ptr
) {
  if (!SV_IS_STRING(str1)) error(NOT_STRING, str1);
  if (!SV_IS_NUM(low)) error(INDEX_NOT_NUM, low);
  if (!SV_IS_NUM(high)) error(INDEX_NOT_NUM, high);

  snake_string_t* ss     = sv_to_string(str1);
  int64_t         low_i  = sv_to_int(low);
  int64_t         high_i = sv_to_int(high);

  if (low_i < 0) { error(SLICE_LOW_INDEX, str1); }
  if (high_i < low_i) { error(SLICE_LOW_INDEX, str1); }
  if ((size_t)high_i > ss->length) { error(SLICE_HIGH_INDEX, str1); }

  size_t slice_length = (size_t)(high_i - low_i);

  uint64_t* alloc_ptr =
      try_gc(sizeof(snake_string_t), cur_base_ptr, cur_stack_ptr);
  snake_string_t* str = (snake_string_t*)alloc_ptr;
  str->length         = slice_length;
  str->string         = ss->string + low_i;

  return pun_ptoi(alloc_ptr) | STRING_TAG;
}

snakeval_t to_int(snakeval_t str) {
  if (!SV_IS_STRING(str)) error(NOT_STRING, str);
  snake_string_t* ss = sv_to_string(str);

  // Making a null-terminated string for use with strol
  char* actual_str = malloc(ss->length + 1);
  memcpy(actual_str, ss->string, ss->length);
  actual_str[ss->length] = '\0';

  char* endptr;
  errno  = 0;
  long i = strtol(actual_str, &endptr, 10);
  bool not_an_int =
      endptr == actual_str || *endptr != '\0' || isspace(actual_str[0]);
  free(actual_str);

  if (errno == ERANGE) {
    error(OVERFLOW, str);
    // unreachable
    return str;
  } else if (not_an_int) {
    error(STRING_NOT_INT, str);
    // unreachable
    return str;
  } else {
    return int_to_sv(i);
  }
}

snakeval_t to_bool(snakeval_t str) {
  if (!SV_IS_STRING(str)) error(NOT_STRING, str);
  snake_string_t* ss = sv_to_string(str);

  if (ss->length == 4 && memcmp("true", ss->string, 4) == 0) {
    return bool_to_sv(true);
  } else if (ss->length == 5 && memcmp("false", ss->string, 5) == 0) {
    return bool_to_sv(false);
  } else {
    error(STRING_NOT_BOOL, str);
    // unreachable
    return str;
  }
}

snakeval_t len(snakeval_t str) {
  if (!SV_IS_STRING(str)) error(NOT_STRING, str);
  snake_string_t* ss = sv_to_string(str);

  return int_to_sv((int64_t)ss->length);
}

/// Reads in user data from stdin. Attempts to parse it as a snake number,
/// boolean, or quoted string. Exits the program if any exceptions occur.
///
/// This reads in characters one at a time. Until it figures out the type it
/// discards all whitespace. If it encounters a non-whitespace character before
/// determining the type it must choose a type or error. It then tries to read
/// the rest of that type.
///
/// \exception
/// - No input left leading to EOF on scan attempt
/// - Parsing an integer would range overflow 64 bits
/// - Parsed integer does not fit snake value constraint
/// - Input is neither boolean, integer, or quoted string
/// - No ending quote when parsing a string
///
/// \param cur_stack_ptr value of \c RSP when called
/// \param cur_base_ptr value of \c RBP when called
/// \return Successfully parsed snake number or boolean
snakeval_t input(uint64_t* const cur_stack_ptr, uint64_t* const cur_base_ptr) {
  str_buf_t       sb         = STR_BUF_INIT;
  bool            fail_eof   = true;
  snakeval_type_t input_type = SV_INVALID;

#define ERROR_INPUT(...)                                                       \
  do {                                                                         \
    fprintf(stderr, __VA_ARGS__);                                              \
    free(sb.buf);                                                              \
    exit(EXIT_FAILURE);                                                        \
  } while (0)

  while (true) {
    const int cur_char = getchar();

    // Fail if we weren't expecting EOF
    if (cur_char == EOF && fail_eof) ERROR_INPUT("Ran out of input: EOF");

    if (isspace(cur_char) || cur_char == EOF) {
      switch (input_type) {
      // Ignore whitespace if we have not chosen a type
      case SV_INVALID: continue;
      case SV_BOOL: {
        if (sb.length == 4 && memcmp("true", sb.buf, 4) == 0) {
          free(sb.buf);
          return bool_to_sv(true);
        } else if (sb.length == 5 && memcmp("false", sb.buf, 5) == 0) {
          free(sb.buf);
          return bool_to_sv(false);
        } else {
          ERROR_INPUT("Unknown input: %.*s\n", (int)sb.length, sb.buf);
        }
      }
      case SV_NUM: {
        // Null terminator for sscanf
        buf_push_char(&sb, '\0');

        int64_t val = 0;
        // Try parsing an integer
        int rv = sscanf(sb.buf, "%ld", &val);
        if (rv == 1) {
          free(sb.buf);
          // Check errno in case the value is too big
          if (errno != 0) {
            perror("Input failed");
            exit(EXIT_FAILURE);
          }
          // Convert integer to snake value and return
          return int_to_sv(val);
        } else {
          ERROR_INPUT("Unknown input: %.*s\n", (int)sb.length, sb.buf);
        }
      }
      case SV_STRING: break;
      case SV_TUPLE:
      case SV_CLOSURE:
      case SV_FWD_PTR:
      case SV_PADDING: assert(false);
      }
    } else if (input_type == SV_INVALID) {
      switch (cur_char) {
        // String opening quote
      case '"': input_type = SV_STRING; continue;
      case 'f':
      case 't': {
        input_type = SV_BOOL;
        fail_eof   = false;
        break;
      }
      case '-':
      case '0':
      case '1':
      case '2':
      case '3':
      case '4':
      case '5':
      case '6':
      case '7':
      case '8':
      case '9': {
        input_type = SV_NUM;
        fail_eof   = false;
        break;
      }
      default: ERROR_INPUT("Unknown input starting with: %c\n", (char)cur_char);
      }
    } else if (input_type == SV_STRING && cur_char == '\"') {
      uint64_t*       alloc_ptr = reserve_str_gc(cur_base_ptr, cur_stack_ptr);
      snake_string_t* str       = (snake_string_t*)alloc_ptr;
      str->length               = sb.length;
      str->string               = sb.buf;

      string_span_t  span = {.string = sb.buf, .length = sb.length};
      str_metadata_t md   = {.visit_idx = 0};

      bool inserted = sbt_insert(&string_map, span, md);
      assert(inserted);
      (void)inserted;

      return pun_ptoi(alloc_ptr) | STRING_TAG;
    }

    buf_push_char(&sb, (char)cur_char);
  }

#undef ERROR_INPUT
}

/// Reads in characters into a string until a new line or end of file is read.
/// The new line is not included. EOF causes an error
/// \param cur_stack_ptr value of \c RSP when called
/// \param cur_base_ptr value of \c RBP when called
/// \return newly allocated string
snakeval_t
readline(uint64_t* const cur_stack_ptr, uint64_t* const cur_base_ptr) {
  str_buf_t sb = STR_BUF_INIT;
  while (true) {
    const int cur_char = getchar();
    if (cur_char == EOF) {
      free(sb.buf);
      fprintf(stderr, "Encounted an EOF in readline");
      exit(EXIT_FAILURE);
    }
    if (cur_char == '\n') break;
    buf_push_char(&sb, (char)cur_char);
  }

  uint64_t*       alloc_ptr = reserve_str_gc(cur_base_ptr, cur_stack_ptr);
  snake_string_t* str       = (snake_string_t*)alloc_ptr;
  str->length               = sb.length;
  str->string               = sb.buf;

  string_span_t  span = {.string = sb.buf, .length = sb.length};
  str_metadata_t md   = {.visit_idx = 0};

  bool inserted = sbt_insert(&string_map, span, md);
  assert(inserted);
  (void)inserted;

  return pun_ptoi(alloc_ptr) | STRING_TAG;
}
