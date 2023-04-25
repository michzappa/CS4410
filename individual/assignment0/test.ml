open OUnit2
open Functions
open Printf

(* a helper for testing integers *)
let t_int name (value : int) (expected : int) =
  name >:: fun _ -> assert_equal expected value ~printer:string_of_int

(* max tests *)
let max_test_negs = t_int "max of two negs" (max (-4) (-2)) (-2)
let max_test_neg_zero = t_int "max of neg and zero" (max (-1) 0) 0
let max_test_zero_pos = t_int "max of zero and pos" (max 0 1) 1
let max_test_poss = t_int "max of two pos's" (max 4 2) 4

(* fibonacci tests *)
let fib_test_neg = t_int "out-of-range index: -1 for fib" (fibonacci (-1)) 1
let fib_test_zero = t_int "out-of-range index: 0 for fib" (fibonacci 0) 1
let fib_test_first = t_int "1st fib number" (fibonacci 1) 1
let fib_test_second = t_int "2nd fib number" (fibonacci 2) 1
let fib_test_third = t_int "3rd fib number" (fibonacci 3) 2
let fib_test_fifth = t_int "5th fib number" (fibonacci 5) 5

(* a helper for testing strings *)
let t_string name (value : string) (expected : string) =
  name >:: fun _ ->
  assert_equal expected value ~printer:(fun s -> sprintf "%S" s)

(* inorder_str tests *)
let leaf_inorder = t_string "inorder_str of a leaf" (inorder_str Leaf) ""

let one_node_inorder =
  t_string "inorder_str of a node" (inorder_str (Node ("a", Leaf, Leaf))) "a"

let left_child_inorder =
  t_string "inorder_str of a node with left child"
    (inorder_str (Node ("a", Node ("b", Leaf, Leaf), Leaf)))
    "ba"

let right_child_inorder =
  t_string "inorder_str of a node with right child"
    (inorder_str (Node ("a", Leaf, Node ("b", Leaf, Leaf))))
    "ab"

let both_children_inorder =
  t_string "inorder_str of a node with both children"
    (inorder_str (Node ("a", Node ("b", Leaf, Leaf), Node ("c", Leaf, Leaf))))
    "bac"

let three_levels_inorder =
  t_string "inorder_str of a full, three-level binary tree"
    (inorder_str
       (Node ("a",
              Node ("b", Node ("c", Leaf, Leaf), Node ("d", Leaf, Leaf)),
              Node ("e", Node ("f", Leaf, Leaf), Node ("g", Leaf, Leaf)))))
    "cbdafeg"

(* size tests, same btnodes as inorder_str *)
let leaf_size = t_int "size of a leaf" (size Leaf) 0

let one_node_size = t_int "size of a node" (size (Node ("a", Leaf, Leaf))) 1

let left_child_size =
  t_int "size of a node with left child"
    (size (Node ("a", Node ("b", Leaf, Leaf), Leaf)))
    2

let right_child_size =
  t_int "size of a node with left child"
    (size (Node ("a", Leaf, Node ("b", Leaf, Leaf))))
    2

let both_children_size =
  t_int "size of a node with both children"
    (size (Node ("a", Node ("b", Leaf, Leaf), Node ("c", Leaf, Leaf))))
    3

let three_levels_size =
  t_int "size of a full, three-level binary tree"
    (size
       (Node ("a",
              Node ("b", Node ("c", Leaf, Leaf), Node ("d", Leaf, Leaf)),
              Node ("e", Node ("f", Leaf, Leaf), Node ("g", Leaf, Leaf)))))
    7

(* height tests, same btnodes as size and inorder_str *)
let leaf_height = t_int "just a leaf" (height Leaf) 0

let one_node_height = t_int "just a node" (height (Node ("a", Leaf, Leaf))) 1

let left_child_height =
  t_int "height of a node with left child"
    (height (Node ("a", Node ("b", Leaf, Leaf), Leaf)))
    2

let right_child_height =
  t_int "height of a node with left child"
    (height (Node ("a", Leaf, Node ("b", Leaf, Leaf))))
    2

let both_children_height =
  t_int "height of a node with both children"
    (height (Node ("a", Node ("b", Leaf, Leaf), Node ("c", Leaf, Leaf))))
    2

let three_levels_height =
  t_int "height of a full, three-level binary tree"
    (height
       (Node ("a",
              Node ("b", Node ("c", Leaf, Leaf), Node ("d", Leaf, Leaf)),
              Node ("e", Node ("f", Leaf, Leaf), Node ("g", Leaf, Leaf)))))
    3

(* helpers for testing lists *)
let string_of_list (stringify : 'a -> string) (list : 'a list) : string =
  sprintf "[%s]" (String.concat "; " (List.map stringify list))

let t_list name (value : 'a list) (expected : 'a list) (stringify : 'a -> string) =
  name >:: fun _ -> assert_equal expected value
                      ~printer:(fun l -> string_of_list stringify l)

let t_int_list name (value : int list) (expected : int list) =
  t_list name value expected string_of_int

let t_string_list name (value : string list) (expected : string list) =
  t_list name value expected (fun s -> s)

(* increment_all tests *)
let increment_empty = t_int_list "increment empty list" (increment_all []) []

let increment_full =
  t_int_list "increment list with multiple elements; positive, negative and zero"
    (increment_all [ 1; 2; 0; -3; -4 ])
    [ 2; 3; 1; -2; -3 ]

(* long_strings tests *)
let long_strings_empty =
  t_string_list "empty list" (long_strings [] 5) [] (* I want property testing *)

let long_strings_full_0 =
  t_string_list "full list, threshold 0" (long_strings [ ""; "1"; "12" ] 0) [ "1"; "12" ]

let long_strings_full_2 =
  t_string_list "full list, threshold 2"
    (long_strings [ ""; "1"; "12"; "123"; "1234" ] 2)
    [ "123"; "1234" ]

(* every_other tests *)
let every_other_empty = t_int_list "empty list" (every_other []) []

let every_other_full =
  t_int_list "every other from a full list"
    (every_other [ 1; 2; 3; 4; 5; 6; 7; 8; 9 ])
    [ 1; 3; 5; 7; 9 ]

(* sum_all tests *)
let sum_empty = t_int_list "empty list" (sum_all []) []

let sum_list_of_empty =
  t_int_list "sublist sums of a list with an empty sub-list" (sum_all [ [] ]) [ 0 ]

let sum_list_of_full =
  t_int_list "sublist sums of a list with some full sub-lists"
    (sum_all [[ 1; 2 ]; []; [ 1; 1; 5 ]])
    [ 3; 0; 7 ]

let suite =
  "suite"
  >:::
    [
      max_test_negs;
      max_test_neg_zero;
      max_test_zero_pos;
      max_test_poss;
      fib_test_neg;
      fib_test_zero;
      fib_test_first;
      fib_test_second;
      fib_test_third;
      fib_test_fifth;
      leaf_inorder;
      one_node_inorder;
      left_child_inorder;
      right_child_inorder;
      both_children_inorder;
      three_levels_inorder;
      leaf_size;
      one_node_size;
      left_child_size;
      right_child_size;
      both_children_size;
      three_levels_size;
      leaf_height;
      one_node_height;
      left_child_height;
      right_child_height;
      both_children_height;
      three_levels_height;
      increment_empty;
      increment_full;
      long_strings_full_0;
      long_strings_full_2;
      every_other_empty;
      every_other_full;
      sum_empty;
      sum_list_of_empty;
      sum_list_of_full;
    ];;

run_test_tt_main suite
