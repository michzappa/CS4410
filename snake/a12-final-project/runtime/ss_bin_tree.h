#ifndef SS_BIN_TREE_H
#define SS_BIN_TREE_H

#include "string_span.h"

#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct sbtnode sbtnode_t;

/// Binary search tree that maps strings spans to metadata. The mapping is done
/// by the unique address for the string span. Two spans that have the same
/// pointer but different lengths would be duplicate keys.
typedef struct ss_bin_tree {
  sbtnode_t* root;
  size_t size;
  size_t max_capacity;
} ss_bin_tree_t;

void sbt_initialize(ss_bin_tree_t* tree, size_t max_capacity);

bool sbt_insert(ss_bin_tree_t* tree, string_span_t key, str_metadata_t value);

int sbt_remove_if(
    ss_bin_tree_t* tree, bool (*predicate)(string_span_t, str_metadata_t)
);

str_metadata_t* sbt_get_from_ptr(ss_bin_tree_t* tree, const char* ptr);

void sbt_destroy(ss_bin_tree_t* tree);

#ifdef __cplusplus
}
#endif

#endif // SS_BIN_TREE_H
