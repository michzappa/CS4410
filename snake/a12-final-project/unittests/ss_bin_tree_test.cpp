#include "ss_bin_tree.h"

#include "test_util.hpp"

#include <gtest/gtest.h>

#include <cstdlib>
#include <string_view>
#include <unordered_set>
#include <utility>

extern "C" {
struct sbtnode {
  sbtnode_t*     left;
  sbtnode_t*     right;
  string_span_t  key;
  str_metadata_t value;
};
}

namespace {

void assert_node(sbtnode_t* node, std::string_view str, str_metadata_t md) {
  ASSERT_NE(node, nullptr);
  ASSERT_NE(node->key.string, nullptr);
  ASSERT_EQ(span_to_view(node->key), str);
  ASSERT_EQ(node->key.length, str.length());
  ASSERT_EQ(node->value.visit_idx, md.visit_idx);
}

std::unordered_set<std::string_view> assert_set_in_tree_help(
    sbtnode_t* node, std::unordered_set<std::string_view> elms
) {
  if (node == NULL) { return elms; }
  elms = assert_set_in_tree_help(node->left, std::move(elms));
  elms = assert_set_in_tree_help(node->right, std::move(elms));

  std::string_view sv = span_to_view(node->key);
  [&] { ASSERT_NE(elms.find(sv), elms.end()); }();

  elms.erase(sv);
  return elms;
}

void assert_set_in_tree(
    ss_bin_tree_t* tree, std::unordered_set<std::string_view> elms
) {
  ASSERT_EQ(tree->size, elms.size());
  elms = assert_set_in_tree_help(tree->root, std::move(elms));
  ASSERT_EQ(elms.size(), 0);
}

TEST(sbt_bin_tree, empty_tree) {
  ss_bin_tree_t tree;
  sbt_initialize(&tree, SIZE_MAX);
  ASSERT_EQ(tree.root, nullptr);
  ASSERT_EQ(tree.size, 0);
  ASSERT_EQ(tree.max_capacity, SIZE_MAX);
  sbt_destroy(&tree);
  ASSERT_EQ(tree.root, nullptr);
}

TEST(sbt_bin_tree, insert_one_element) {
  ss_bin_tree_t tree;
  sbt_initialize(&tree, SIZE_MAX);

  sbt_insert(&tree, alloc_span("hello"), {0});
  assert_node(tree.root, "hello", {0});
  ASSERT_EQ(tree.size, 1);

  sbt_destroy(&tree);
  ASSERT_EQ(tree.root, nullptr);
}

TEST(sbt_bin_tree, insert_two_elements) {
  ss_bin_tree_t tree;
  sbt_initialize(&tree, SIZE_MAX);

  string_span_t spans[] = {
      alloc_span("hello"),
      alloc_span("goodbye"),
  };

  sbt_insert(&tree, spans[0], {0});
  assert_node(tree.root, "hello", {0});
  ASSERT_EQ(tree.size, 1);

  sbt_insert(&tree, spans[1], {0});
  if (tree.root->left == nullptr) {
    assert_node(tree.root->right, "goodbye", {0});
  } else {
    assert_node(tree.root->left, "goodbye", {0});
  }

  assert_set_in_tree(&tree, {"hello", "goodbye"});

  sbt_destroy(&tree);
  ASSERT_EQ(tree.root, nullptr);
}

TEST(sbt_bin_tree, many_element_tree) {
  ss_bin_tree_t tree;
  sbt_initialize(&tree, SIZE_MAX);

  string_span_t spans[] = {
      alloc_span("hello"),
      alloc_span("goodbye"),
      alloc_span("dave"),
      alloc_span("sus"),
      alloc_span("batman"),
      alloc_span("cheese"),
      alloc_span("some really long sentence"),
      alloc_span("/n/t/rfasdfaisdf;asdif asd fksl;ad jfasdpi fjasldfj x9dc8 "
                 "c9weoirso9dfyaewr"),
  };

  for (string_span_t span : spans) { sbt_insert(&tree, span, {0}); }

  std::unordered_set<std::string_view> sv_set;
  for (string_span_t span : spans) { sv_set.insert(span_to_view(span)); }

  assert_set_in_tree(&tree, std::move(sv_set));

  sbt_destroy(&tree);
  ASSERT_EQ(tree.root, nullptr);
}

TEST(sbt_bin_tree, remove_on_predicate) {
  ss_bin_tree_t tree;
  sbt_initialize(&tree, SIZE_MAX);

  string_span_t spans[] = {
      alloc_span("hello"),
      alloc_span("goodbye"),
      alloc_span("dave"),
      alloc_span("sus"),
      alloc_span("batman"),
      alloc_span("cheese"),
      alloc_span("some really long sentence"),
      alloc_span("/n/t/rfasdfaisdf;asdif asd fksl;ad jfasdpi fjasldfj x9dc8 "
                 "c9weoirso9dfyaewr"),
  };

  for (string_span_t span : spans) { sbt_insert(&tree, span, {0}); }

  std::unordered_set<std::string_view> sv_set;
  for (string_span_t span : spans) { sv_set.insert(span_to_view(span)); }

  assert_set_in_tree(&tree, sv_set);

  // Must remove from set before sbt_remove_if or else dangling ptr
  std::erase_if(sv_set, [](std::string_view sv) { return sv.length() < 5; });
  ASSERT_NE(sv_set.size(), std::size(spans));

  sbt_remove_if(&tree, [](string_span_t s, auto) { return s.length < 5; });

  assert_set_in_tree(&tree, std::move(sv_set));

  sbt_destroy(&tree);
  ASSERT_EQ(tree.root, nullptr);
}

TEST(sbt_bin_tree, remove_nothing) {
  ss_bin_tree_t tree;
  sbt_initialize(&tree, SIZE_MAX);

  string_span_t spans[] = {
      alloc_span("hello"),
      alloc_span("goodbye"),
      alloc_span("dave"),
      alloc_span("sus"),
      alloc_span("batman"),
      alloc_span("cheese"),
      alloc_span("some really long sentence"),
      alloc_span("/n/t/rfasdfaisdf;asdif asd fksl;ad jfasdpi fjasldfj x9dc8 "
                 "c9weoirso9dfyaewr"),
  };

  for (string_span_t span : spans) { sbt_insert(&tree, span, {0}); }

  std::unordered_set<std::string_view> sv_set;
  for (string_span_t span : spans) { sv_set.insert(span_to_view(span)); }

  assert_set_in_tree(&tree, sv_set);

  sbt_remove_if(&tree, [](auto, auto) { return false; });

  assert_set_in_tree(&tree, std::move(sv_set));

  sbt_destroy(&tree);
  ASSERT_EQ(tree.root, nullptr);
}

TEST(sbt_bin_tree, get_from_ptr) {
  ss_bin_tree_t tree;
  sbt_initialize(&tree, SIZE_MAX);

  string_span_t spans[] = {
      alloc_span("m"),
      alloc_span("l"),
      alloc_span("n"),
      alloc_span("k"),
      alloc_span("o"),
  };

  for (uint8_t index = 0; string_span_t span : spans) {
    sbt_insert(&tree, span, {index++});
  }

  std::unordered_set<std::string_view> sv_set;
  for (string_span_t span : spans) { sv_set.insert(span_to_view(span)); }

  assert_set_in_tree(&tree, sv_set);

  str_metadata_t* not_found = sbt_get_from_ptr(&tree, "z");
  ASSERT_EQ(not_found, nullptr);

  for (uint8_t index = 0; string_span_t span : spans) {
    str_metadata_t* found = sbt_get_from_ptr(&tree, span.string);
    ASSERT_EQ(found->visit_idx, index);
    index += 1;
  }

  sbt_destroy(&tree);
  ASSERT_EQ(tree.root, nullptr);
}

TEST(sbt_bin_tree, null_input) {
  ASSERT_DEATH({ sbt_initialize(NULL, 0); }, "tree != NULL");
  ASSERT_DEATH({ sbt_insert(NULL, {}, {}); }, "tree != NULL");
  ASSERT_DEATH(
      { sbt_remove_if(NULL, [](auto...) { return false; }); }, "tree != NULL"
  );
  ASSERT_DEATH(
      {
        ss_bin_tree_t tree;
        sbt_initialize(&tree, SIZE_MAX);
        sbt_remove_if(&tree, NULL);
      },
      "predicate != NULL"
  );
  ASSERT_DEATH({ sbt_get_from_ptr(NULL, "hello"); }, "tree != NULL");
  ASSERT_DEATH({ sbt_destroy(NULL); }, "tree != NULL");
}

TEST(sbt_bin_tree, insert_too_many) {
  ASSERT_DEATH(
      {
        ss_bin_tree_t tree;
        sbt_initialize(&tree, 0);
        sbt_insert(&tree, alloc_span("hello"), {0});
      },
      "tree->size < tree->max_capacity"
  );
}
} // namespace
