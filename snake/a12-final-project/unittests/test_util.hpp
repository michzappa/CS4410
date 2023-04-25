#ifndef TEST_UTIL_HPP
#define TEST_UTIL_HPP

#include "string_span.h"

#include <cstdlib>
#include <cstring>
#include <string_view>

inline string_span_t alloc_span(std::string_view str) {
  string_span_t s;
  s.length     = str.length();
  char* memstr = (char*)calloc(s.length, sizeof(*memstr));
  memcpy(memstr, str.data(), s.length);
  s.string = memstr;
  return s;
}

inline std::string_view span_to_view(string_span_t span) {
  return std::string_view(span.string, span.length);
}

inline string_span_t view_to_span(std::string_view view) {
  return {view.data(), view.length()};
}

#endif // TEST_UTIL_HPP
