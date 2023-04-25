
#include "string_span.h"

#include "test_util.hpp"

#include <gtest/gtest.h>

#include <ranges>
#include <utility>

namespace {

TEST(string_span, destroy) {
  string_span_t s = alloc_span("hello");
  ASSERT_NE(s.string, nullptr);
  ASSERT_EQ(s.length, 5);
  ASSERT_EQ(span_to_view(s), "hello");
  string_span_destroy(s);
}

TEST(string_span, compare) {
  std::string_view buf = "hello goodbye";
  string_span_t    s1  = {&buf[0], 5};
  string_span_t    s2  = {&buf[6], 7};
  string_span_t    s3  = {&buf[1], 2};

  ASSERT_EQ(string_span_cmp(s1, s1), 0);
  ASSERT_EQ(string_span_cmp(s2, s2), 0);
  ASSERT_EQ(string_span_cmp(s3, s3), 0);

  ASSERT_LT(string_span_cmp(s1, s2), 0);
  ASSERT_GT(string_span_cmp(s2, s1), 0);

  ASSERT_LT(string_span_cmp(s1, s3), 0);
  ASSERT_GT(string_span_cmp(s3, s1), 0);

  ASSERT_LT(string_span_cmp(s3, s2), 0);
  ASSERT_GT(string_span_cmp(s2, s3), 0);
}

TEST(string_span, compare_regression) {
  char*         p1 = (char*)0x604000000010;
  char*         p2 = (char*)0x602000000010;
  string_span_t s1 = {p1, 5};
  string_span_t s2 = {p2, 7};

  ASSERT_EQ(string_span_cmp(s1, s1), 0);
  ASSERT_EQ(string_span_cmp(s2, s2), 0);

  ASSERT_GT(string_span_cmp(s1, s2), 0);
  ASSERT_LT(string_span_cmp(s2, s1), 0);
}

TEST(string_span, contain) {
  std::string_view buf = "hello goodbye";
  string_span_t    s1  = {&buf[0], 5};
  string_span_t    s2  = {&buf[6], 7};
  string_span_t    s3  = {&buf[1], 2};

  for (size_t idx : std::views::iota(0, 13)) {
    ASSERT_EQ(string_span_contain(s1, &buf[idx]), idx < 5);
    ASSERT_EQ(string_span_contain(s2, &buf[idx]), idx >= 6);
    ASSERT_EQ(string_span_contain(s3, &buf[idx]), 1 <= idx && idx < 3);
  }
}

} // namespace
