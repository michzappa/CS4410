#include "ss_bin_tree.h"

#include "string_span.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct sbtnode {
  sbtnode_t*     left;
  sbtnode_t*     right;
  string_span_t  key;
  str_metadata_t value;
};

#define TEMP_TREE(...)                                                         \
  { __VA_ARGS__, 0, SIZE_MAX }

static sbtnode_t* new_node(
    sbtnode_t* const     left,
    sbtnode_t* const     right,
    const string_span_t  key,
    const str_metadata_t value
) {
  sbtnode_t* node = calloc(1, sizeof(*node));
  assert(node != NULL);
  memset(node, 0, sizeof(*node));
  node->left  = left;
  node->right = right;
  node->key   = key;
  node->value = value;
  return node;
}

static bool
sbt_insert_node(ss_bin_tree_t* const tree, sbtnode_t* const node_to_insert) {
  if (node_to_insert == NULL) { return false; }

  assert(tree != NULL);
  if (tree->root == NULL) {
    tree->root = node_to_insert;
    return true;
  }

  sbtnode_t* cursor = tree->root;
  while (true) {
    int cmp = string_span_cmp(cursor->key, node_to_insert->key);
    if (cmp == 0) {
      // key already exists so do not insert
      return false;
    }

    if (cmp < 0) {
      // cursor is less that key so go right
      if (cursor->right == NULL) {
        cursor->right = node_to_insert;
        return true;
      }
      cursor = cursor->right;
    } else {
      // cursor is greater than key so go left
      if (cursor->left == NULL) {
        cursor->left = node_to_insert;
        return true;
      }
      cursor = cursor->left;
    }
  }
}

void sbt_initialize(ss_bin_tree_t* const tree, size_t max_capacity) {
  assert(tree != NULL);
  tree->root         = NULL;
  tree->size         = 0;
  tree->max_capacity = max_capacity;
}

/// Attempts to insert a string and metadata pair if the string is not already
/// contained by tree.
///
/// \note Tree will take ownership over the string span and attempt to free the
/// memory during removal.
///
/// \param tree tree to attempt an insert on
/// \param key string that is used for position on the tree
/// \param value metadata that is mapped to by the key
/// \return true iff the key was not found and therefore inserted
bool sbt_insert(
    ss_bin_tree_t* const tree,
    const string_span_t  key,
    const str_metadata_t value
) {
  assert(tree != NULL);
  assert(tree->size < tree->max_capacity);

  sbtnode_t* node_to_insert = new_node(NULL, NULL, key, value);
  bool       was_insert     = sbt_insert_node(tree, node_to_insert);
  if (was_insert) { tree->size += 1; }
  return was_insert;
}

static int sbt_remove_if_impl(
    ss_bin_tree_t* const tree,
    bool (*const predicate)(string_span_t, str_metadata_t)
) {
  assert(tree != NULL);
  assert(predicate != NULL);
  if (tree->root == NULL) { return 0; }

  int delete_cnt = 0;

  ss_bin_tree_t left_tree  = TEMP_TREE(tree->root->left);
  ss_bin_tree_t right_tree = TEMP_TREE(tree->root->right);

  delete_cnt += sbt_remove_if(&left_tree, predicate);
  delete_cnt += sbt_remove_if(&right_tree, predicate);

  if (predicate(tree->root->key, tree->root->value)) {
    string_span_destroy(tree->root->key);
    free(tree->root);

    tree->root = left_tree.root;
    sbt_insert_node(tree, right_tree.root);
    return delete_cnt + 1;
  } else {
    tree->root->left  = left_tree.root;
    tree->root->right = right_tree.root;
    return delete_cnt;
  }
}

int sbt_remove_if(
    ss_bin_tree_t* const tree,
    bool (*const predicate)(string_span_t, str_metadata_t)
) {
  int remove_cnt = sbt_remove_if_impl(tree, predicate);
  tree->size -= (size_t)remove_cnt;
  return remove_cnt;
}

/// Recurses over the tree and checks if the pointer is contained in any of the
/// keys. If a containing key is found then its metadata is returned, otherwise
/// null.
/// \param tree tree to search over for a containing key
/// \param ptr string point that will be checked if it is contained by any of
/// the keys
/// \return Point to the meta data for the passed in string pointer or returns
/// null if the string pointer was not found in any node
str_metadata_t*
sbt_get_from_ptr(ss_bin_tree_t* const tree, const char* const ptr) {
  assert(tree != NULL);

  if (tree->root == NULL) { return NULL; }

  if (string_span_contain(tree->root->key, ptr)) { return &tree->root->value; }

  ss_bin_tree_t   left_tree  = TEMP_TREE(tree->root->left);
  str_metadata_t* found_left = sbt_get_from_ptr(&left_tree, ptr);
  if (found_left != NULL) { return found_left; }

  ss_bin_tree_t right_tree = TEMP_TREE(tree->root->right);
  return sbt_get_from_ptr(&right_tree, ptr);
}

/// Call back for remove if that always returns true
static bool return_true(string_span_t s, str_metadata_t m) {
  (void)s;
  (void)m;
  return true;
}

/// Recurses over the tree and removes every node while freeing the memory
/// \param tree tree to remove and free all nodes from
void sbt_destroy(ss_bin_tree_t* tree) { sbt_remove_if(tree, return_true); }
