open Anf
open Assembly
open Utils
open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Environment

let t_any name value expected =
  name >:: fun _ -> assert_equal expected value ~printer:ExtLib.dump
;;

let t name program ?(input = "") expected =
  name >:: test_run ~args:[] ~std_input:input program name expected
;;

let ta name program ?(input = "") expected =
  name >:: test_run_anf ~args:[] ~std_input:input program name expected
;;

let tgc name heap_size program ?(input = "") expected =
  name
  >:: test_run
        ~args:[string_of_int heap_size]
        ~std_input:input program name expected
;;

let tvg name program ?(input = "") expected =
  name >:: test_run_valgrind ~args:[] ~std_input:input program name expected
;;

let tvgc name heap_size program ?(input = "") expected =
  name
  >:: test_run_valgrind
        ~args:[string_of_int heap_size]
        ~std_input:input program name expected
;;

let terr name program ?(input = "") expected =
  name >:: test_err ~args:[] ~std_input:input program name expected
;;

let tgcerr name heap_size program ?(input = "") expected =
  name
  >:: test_err
        ~args:[string_of_int heap_size]
        ~std_input:input program name expected
;;

let tanf name program expected =
  name
  >:: fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

let tparse name program expected =
  name
  >:: fun _ ->
  assert_equal (untagP expected)
    (untagP (parse_string name program))
    ~printer:string_of_program
;;

let teq name actual expected =
  name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)
;;

let tfvs name program expected =
  name
  >:: fun _ ->
  let ast = parse_string name program in
  let anfed = anf (tag ast) in
  match anfed with
  | AProgram (body, _) ->
      let vars = free_vars body in
      let c = Stdlib.compare in
      let str_list_print strs = "[" ^ ExtString.String.join ", " strs ^ "]" in
      assert_equal (List.sort c vars) (List.sort c expected)
        ~printer:str_list_print
;;

let collect_duplicates_suite =
  [ t_any "cd_empty_list" (collect_duplicates []) [];
    t_any "cd_list_len1" (collect_duplicates [3]) [];
    t_any "cd_two_dup_len2" (collect_duplicates [3; 3]) [3];
    t_any "cd_three_same_len3" (collect_duplicates ['a'; 'a'; 'a']) ['a'];
    t_any "cd_dups_interspersed0"
      (collect_duplicates [3; 1; 2; 3; 5; 6; 1])
      [3; 1];
    t_any "cd_dups_interspersed1"
      (collect_duplicates ["a"; "b"; "b"; "c"; "b"; "d"; "b"])
      ["b"];
    t_any "cd_dups_repeat_substr"
      (collect_duplicates
         ["a"; "b"; "c"; "d"; "a"; "b"; "c"; "d"; "a"; "b"; "c"; "d"] )
      ["a"; "b"; "c"; "d"];
    t_any "cd_no_dups_big_list"
      (collect_duplicates [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 10000])
      [] ]
;;

let enumerate_suite =
  [ t_any "enum0_empty" (enumerate []) [];
    t_any "enum1_singleton" (enumerate ["hello"]) [(0, "hello")];
    t_any "enum2_long_list"
      (enumerate ['a'; 'b'; 'd'; 'c'; 'e'; 'f'])
      [(0, 'a'); (1, 'b'); (2, 'd'); (3, 'c'); (4, 'e'); (5, 'f')] ]
;;

let collect_arg_cycles_suite =
  [ t_any "cycle0_empty_both" (collect_arg_cycles [] []) [];
    t_any "cycle1_empty_caller" (collect_arg_cycles [] [ImmBool (true, ())]) [];
    t_any "cycle2_empty_caller"
      (collect_arg_cycles [] [ImmId ("a", ()); ImmId ("b", ())])
      [];
    t_any "cycle3_empty_args" (collect_arg_cycles ["a"; "b"; "c"] []) [];
    t_any "cycle4_single_both_diff"
      (collect_arg_cycles ["a"] [ImmBool (true, ())])
      [];
    t_any "cycle5_single_both_diff"
      (collect_arg_cycles ["a"] [ImmId ("b", ())])
      [];
    t_any "cycle6_single_both_match"
      (collect_arg_cycles ["a"] [ImmId ("a", ())])
      [[(0, ("a", ()))]];
    t_any "cycle7_multiple_all_match"
      (collect_arg_cycles ["x"; "y"; "z"]
         [ImmId ("x", ()); ImmId ("y", ()); ImmId ("z", ())] )
      [[(0, ("x", ()))]; [(1, ("y", ()))]; [(2, ("z", ()))]];
    t_any "cycle9_both_three_shl_cycle"
      (collect_arg_cycles ["a"; "b"; "c"]
         [ImmId ("b", ()); ImmId ("c", ()); ImmId ("a", ())] )
      [[(0, ("b", ())); (1, ("c", ())); (2, ("a", ()))]];
    t_any "cycle10_both_three_shr_cycle"
      (collect_arg_cycles ["a"; "b"; "c"]
         [ImmId ("c", ()); ImmId ("a", ()); ImmId ("b", ())] )
      [[(0, ("c", ())); (2, ("b", ())); (1, ("a", ()))]];
    t_any "cycle11_both_three_two_cycle"
      (collect_arg_cycles ["a"; "b"; "c"]
         [ImmId ("b", ()); ImmId ("a", ()); ImmId ("c", ())] )
      [[(0, ("b", ())); (1, ("a", ()))]; [(2, ("c", ()))]];
    t_any "cycle12_both_three_two_cycle"
      (collect_arg_cycles ["a"; "b"; "c"]
         [ImmId ("c", ()); ImmId ("b", ()); ImmId ("a", ())] )
      [[(0, ("c", ())); (2, ("a", ()))]; [(1, ("b", ()))]];
    t_any "cycle13_both_three_two_cycle"
      (collect_arg_cycles ["a"; "b"; "c"]
         [ImmId ("z", ()); ImmId ("a", ()); ImmId ("b", ())] )
      [[(1, ("a", ())); (2, ("b", ()))]];
    t_any "cycle14_both_three_one_cycle"
      (collect_arg_cycles ["a"; "b"; "c"]
         [ImmNum (3L, ()); ImmId ("a", ()); ImmId ("z", ())] )
      [[(1, ("a", ()))]];
    t_any "cycle15_arg_greater_no_match"
      (collect_arg_cycles ["a"; "b"; "c"; "d"]
         [ImmId ("x", ()); ImmId ("y", ())] )
      [];
    t_any "cycle16_arg_greater_one_match"
      (collect_arg_cycles ["a"; "b"; "c"; "d"]
         [ImmId ("a", ()); ImmId ("y", ())] )
      [[(0, ("a", ()))]];
    t_any "cycle17_arg_greater_one_diff_pos"
      (collect_arg_cycles ["a"; "b"; "c"; "d"]
         [ImmId ("x", ()); ImmId ("d", ())] )
      [[(1, ("d", ()))]];
    t_any "cycle18_arg_greater_two_self_cycle"
      (collect_arg_cycles ["a"; "b"; "c"; "d"]
         [ImmId ("b", ()); ImmId ("z", ()); ImmId ("d", ())] )
      [[(0, ("b", ()))]; [(2, ("d", ()))]];
    t_any "cycle19_arg_greater_two_in_cycle"
      (collect_arg_cycles ["a"; "b"; "c"; "d"]
         [ImmId ("c", ()); ImmId ("z", ()); ImmId ("b", ())] )
      [[(0, ("c", ())); (2, ("b", ()))]];
    t_any "cycle20_both_three_shr_cycle_ignore_middle"
      (collect_arg_cycles ["a"; "b"; "c"]
         [ImmId ("c", ()); ImmId ("a", ()); ImmNum (1L, ())] )
      [[(0, ("c", ())); (1, ("a", ()))]] ]
;;

let naive_stack_allocation_suite =
  [ (let ast =
       AProgram
         ( ALetRec
             ( [("x", CLambda ([], ACExpr (CImmExpr (ImmNum (1L, 1))), [], 2))],
               ACExpr (CImmExpr (ImmNum (1L, 3))),
               4 ),
           0 )
     in
     t_any "sa_let_rec_1"
       (naive_stack_allocation ast)
       (ast, [("x", RegOffset (~-8, RBP))]) );
    (let ast =
       AProgram
         ( ALetRec
             ( [ ("x", CLambda ([], ACExpr (CImmExpr (ImmNum (1L, 1))), [], 2));
                 ("y", CLambda ([], ACExpr (CImmExpr (ImmNum (2L, 3))), [], 4));
                 ("z", CLambda ([], ACExpr (CImmExpr (ImmNum (2L, 5))), [], 6))
               ],
               ACExpr (CImmExpr (ImmNum (1L, 7))),
               8 ),
           0 )
     in
     t_any "sa_let_rec_2"
       (naive_stack_allocation ast)
       ( ast,
         [ ("x", RegOffset (~-8, RBP));
           ("y", RegOffset (~-16, RBP));
           ("z", RegOffset (~-24, RBP)) ] ) );
    (let ast = AProgram (ACExpr (CImmExpr (ImmNum (1L, 1))), 0) in
     t_any "sa_empty_program" (naive_stack_allocation ast) (ast, []) );
    (let aexp = ACExpr (CImmExpr (ImmNum (1L, 1))) in
     let _, env = naive_stack_allocation (AProgram (aexp, 0)) in
     t_any "sa_empty_program_count" (deepest_stack aexp env) (count_vars aexp)
    );
    (let ast =
       AProgram
         ( ALet
             ( "x",
               CImmExpr (ImmNum (1L, 1)),
               ACExpr (CImmExpr (ImmNum (1L, 2))),
               1 ),
           0 )
     in
     t_any "sa_no_decls_let_1"
       (naive_stack_allocation ast)
       (ast, [("x", RegOffset (~-8, RBP))]) );
    (let aexp =
       ALet
         ("x", CImmExpr (ImmNum (1L, 1)), ACExpr (CImmExpr (ImmNum (1L, 2))), 1)
     in
     let _, env = naive_stack_allocation (AProgram (aexp, 0)) in
     t_any "sa_no_decls_let_1_count" (deepest_stack aexp env) (count_vars aexp)
    );
    (let ast =
       AProgram
         ( ALet
             ( "x",
               CImmExpr (ImmNum (1L, 7)),
               ALet
                 ( "y",
                   CImmExpr (ImmNum (1L, 6)),
                   ALet
                     ( "z",
                       CImmExpr (ImmNum (1L, 5)),
                       ACExpr (CImmExpr (ImmNum (1L, 4))),
                       3 ),
                   2 ),
               1 ),
           0 )
     in
     t_any "sa_no_decls_let_2"
       (naive_stack_allocation ast)
       ( ast,
         [ ("x", RegOffset (~-8, RBP));
           ("y", RegOffset (~-16, RBP));
           ("z", RegOffset (~-24, RBP)) ] ) );
    (let aexp =
       ALet
         ( "x",
           CImmExpr (ImmNum (1L, 7)),
           ALet
             ( "y",
               CImmExpr (ImmNum (1L, 6)),
               ALet
                 ( "z",
                   CImmExpr (ImmNum (1L, 5)),
                   ACExpr (CImmExpr (ImmNum (1L, 4))),
                   3 ),
               2 ),
           1 )
     in
     let _, env = naive_stack_allocation (AProgram (aexp, 0)) in
     t_any "sa_no_decls_let_2_count" (deepest_stack aexp env) (count_vars aexp)
    );
    (let aexp =
       ALet
         ( "x",
           CImmExpr (ImmNum (1L, 7)),
           ACExpr
             (CLPrim2
                ( And,
                  ImmBool (true, 4),
                  ALet
                    ( "y",
                      CImmExpr (ImmNum (1L, 6)),
                      ALet
                        ( "z",
                          CImmExpr (ImmNum (1L, 5)),
                          ACExpr (CImmExpr (ImmNum (1L, 4))),
                          3 ),
                      2 ),
                  1 ) ),
           5 )
     in
     let _, env = naive_stack_allocation (AProgram (aexp, 0)) in
     t_any "sa_one_decls_let_count" (deepest_stack aexp env) (count_vars aexp)
    );
    (let ast =
       AProgram
         ( ALet
             ( "f",
               CLambda
                 ( ["farg1"; "farg2"; "farg3"],
                   ACExpr (CImmExpr (ImmNum (1L, 9))),
                   [],
                   8 ),
               ALet
                 ( "x",
                   CImmExpr (ImmNum (1L, 7)),
                   ALet
                     ( "y",
                       CImmExpr (ImmNum (1L, 6)),
                       ALet
                         ( "z",
                           CImmExpr (ImmNum (1L, 5)),
                           ACExpr (CImmExpr (ImmNum (1L, 4))),
                           3 ),
                       2 ),
                   1 ),
               10 ),
           0 )
     in
     t_any "sa_one_decls_let"
       (naive_stack_allocation ast)
       ( ast,
         [ ("f", RegOffset (~-8, RBP));
           ("farg1", RegOffset (24, RBP));
           ("farg2", RegOffset (32, RBP));
           ("farg3", RegOffset (40, RBP));
           ("x", RegOffset (~-16, RBP));
           ("y", RegOffset (~-24, RBP));
           ("z", RegOffset (~-32, RBP)) ] ) );
    (let ast =
       AProgram
         ( (* [ ADFun *)
           (*     ( "f", *)
           (*       ["farg1"; "farg2"; "farg3"], *)
           (*       ACExpr (CImmExpr (ImmNum (1L, 9))), *)
           (*       8 ); *)
           (*   ADFun *)
           (*     ( "g", *)
           (*       ["garg1"; "garg2"; "garg3"], *)
           (*       ACExpr (CImmExpr (ImmNum (1L, 10))), *)
           (*       11 ) ], *)
           ALet
             ( "f",
               CLambda
                 ( ["farg1"; "farg2"; "farg3"],
                   ACExpr (CImmExpr (ImmNum (1L, 9))),
                   [],
                   8 ),
               ALet
                 ( "g",
                   CLambda
                     ( ["garg1"; "garg2"; "garg3"],
                       ACExpr (CImmExpr (ImmNum (1L, 9))),
                       [],
                       11 ),
                   ALet
                     ( "x",
                       CImmExpr (ImmNum (1L, 7)),
                       ALet
                         ( "y",
                           CImmExpr (ImmNum (1L, 6)),
                           ALet
                             ( "z",
                               CImmExpr (ImmNum (1L, 5)),
                               ACExpr (CImmExpr (ImmNum (1L, 4))),
                               3 ),
                           2 ),
                       1 ),
                   10 ),
               11 ),
           0 )
     in
     t_any "sa_two_decls"
       (naive_stack_allocation ast)
       ( ast,
         [ ("f", RegOffset (~-8, RBP));
           ("farg1", RegOffset (24, RBP));
           ("farg2", RegOffset (32, RBP));
           ("farg3", RegOffset (40, RBP));
           ("g", RegOffset (~-16, RBP));
           ("garg1", RegOffset (24, RBP));
           ("garg2", RegOffset (32, RBP));
           ("garg3", RegOffset (40, RBP));
           ("x", RegOffset (~-24, RBP));
           ("y", RegOffset (~-32, RBP));
           ("z", RegOffset (~-40, RBP)) ] ) ) ]
;;

let well_formedness_suite =
  [ (* Ensure all detectable errors are printed *)
    terr "wf_unbound_id_plus_1" "a + b"
      "The identifier a, used at <wf_unbound_id_plus_1, 1:0-1:1>, is not in \
       scope\n\
       The identifier b, used at <wf_unbound_id_plus_1, 1:4-1:5>, is not in \
       scope";
    terr "wf_unbound_id_plus_2" "a + b"
      "The identifier a, used at <wf_unbound_id_plus_2, 1:0-1:1>, is not in \
       scope\n\
       The identifier b, used at <wf_unbound_id_plus_2, 1:4-1:5>, is not in \
       scope";
    terr "wf_duplicate_id_let_1" "let x = 3, x = 4 in y + z"
      "The identifier x, redefined at <wf_duplicate_id_let_1, 1:11-1:12>, \
       duplicates one at <wf_duplicate_id_let_1, 1:4-1:5>\n\
       The identifier y, used at <wf_duplicate_id_let_1, 1:20-1:21>, is not in \
       scope\n\
       The identifier z, used at <wf_duplicate_id_let_1, 1:24-1:25>, is not in \
       scope";
    terr "wf_unbound_id_let_plus_1" "let x = 3, x = 4 in y + z"
      "The identifier x, redefined at <wf_unbound_id_let_plus_1, 1:11-1:12>, \
       duplicates one at <wf_unbound_id_let_plus_1, 1:4-1:5>\n\
       The identifier y, used at <wf_unbound_id_let_plus_1, 1:20-1:21>, is not \
       in scope\n\
       The identifier z, used at <wf_unbound_id_let_plus_1, 1:24-1:25>, is not \
       in scope";
    terr "wf_unbound_id_let_plus_2" "let x = 3, x = 4 in y + z"
      "The identifier x, redefined at <wf_unbound_id_let_plus_2, 1:11-1:12>, \
       duplicates one at <wf_unbound_id_let_plus_2, 1:4-1:5>\n\
       The identifier y, used at <wf_unbound_id_let_plus_2, 1:20-1:21>, is not \
       in scope\n\
       The identifier z, used at <wf_unbound_id_let_plus_2, 1:24-1:25>, is not \
       in scope";
    terr "wf_duplicate_in_let_binding" "let (x, x, (y, y)) = 3 in x"
      "The identifier x, redefined at <wf_duplicate_in_let_binding, 1:8-1:9>, \
       duplicates one at <wf_duplicate_in_let_binding, 1:5-1:6>\n\
       The identifier y, redefined at <wf_duplicate_in_let_binding, \
       1:15-1:16>, duplicates one at <wf_duplicate_in_let_binding, 1:12-1:13>";
    terr "wf_shadow_builtin" "def print(x, y): x + y\nprint(3, 4)"
      "The identifier print, defined at <wf_shadow_builtin, 1:0-1:22>, shadows \
       a builtin identifier" ]
;;

(* TODO potentially move these tests into the input file system, but first rename those that exist there already *)

(* There are more 'let' tests in the input_file_test_suite *)
let let_suite =
  [ t "forty" "let x = 40 in x" "40";
    t "fals" "let x = false in x" "false";
    t "tru" "let x = true in x" "true";
    t "shadow" "let x = 1 in let x = 2 in x" "2";
    t "manybinds" "let a = 1, b = 2, c = 3, d = 4 in b" "2";
    t "letx2" "let x = 2 in x" "2" ]
;;

let prim1_suite =
  [ t "prim1_1" "add1(1)" "2";
    t "prim1_2" "sub1(1)" "0";
    t "prim1_3" "isbool(true)" "true";
    t "prim1_4" "isbool(4)" "false";
    t "prim1_5" "isnum(4)" "true";
    t "prim1_6" "isnum(true)" "false";
    t "prim1_7" "!(true)" "false";
    t "prim1_8" "!(false)" "true";
    (* Exception checks *)
    terr "prim1_e_1" "!(4)" "logic expected a boolean, got: 4";
    terr "prim1_e_2" "add1(true)" "arithmetic expected a number, got: true";
    terr "prim1_e_3" "sub1(false)" "arithmetic expected a number, got: false";
    terr "prim1_e_4" "add1(4611686018427387903)" "overflow occurred";
    terr "prim1_e_5" "sub1(-4611686018427387904)" "overflow occurred" ]
;;

let prim2_logic_suite =
  [ t "prim2_logic_or_0" "true || true" "true";
    t "prim2_logic_or_1" "true || false" "true";
    t "prim2_logic_or_2" "false || true" "true";
    t "prim2_logic_or_3" "false || false" "false";
    t "prim2_logic_or_4" "true || 4" "true";
    t "prim2_logic_or_5" "true || print(true)" "true";
    t "prim2_logic_or_6" "true || print(false)" "true";
    t "prim2_logic_or_7" "print(false) || print(true)" "false\ntrue\ntrue";
    t "prim2_logic_and_0" "true && true" "true";
    t "prim2_logic_and_1" "true && false" "false";
    t "prim2_logic_and_2" "false && true" "false";
    t "prim2_logic_and_3" "false && false" "false";
    t "prim2_logic_and_4" "false && 4" "false";
    t "prim2_logic_and_5" "false && print(true)" "false";
    t "prim2_logic_and_6" "false && print(false)" "false";
    t "prim2_logic_and_7" "print(true) && print(false)" "true\nfalse\nfalse";
    (* Exception checks *)
    terr "prim2_logic_or_e_1" "4 || true" "logic expected a boolean, got: 4";
    terr "prim2_logic_or_e_2" "false || 4" "logic expected a boolean, got: 4";
    terr "prim2_logic_or_e_3" "1 || 4" "logic expected a boolean, got: 1";
    terr "prim2_logic_and_e_1" "4 && true" "logic expected a boolean, got: 4";
    terr "prim2_logic_and_e_2" "true && 4" "logic expected a boolean, got: 4";
    terr "prim2_logic_and_e_3" "1 && 4" "logic expected a boolean, got: 1";
    terr "prim2_arith_add_e_1" "true + 1"
      "arithmetic expected a number, got: true";
    terr "prim2_arith_add_e_2" "1 + true"
      "arithmetic expected a number, got: true";
    terr "prim2_arith_add_e_3" "true + false"
      "arithmetic expected a number, got: true" ]
;;

let prim2_arith_suite =
  [ t "many_adds" "1+2+3+4+5+6" "21";
    t "many_adds_then_neg" "1+2+3+4+5+-6" "9";
    t "many_prim2s" "1 + 2 * 3 - 4 + 5" "10";
    t "1sub5" "1 - 5" "-4";
    t "prim2_arith_plus_1" "1 + 1" "2";
    t "prim2_arith_plus_2" "1 + 10000000000000" "10000000000001";
    t "prim2_arith_plus_3" "10000000000000 + 1" "10000000000001";
    t "prim2_arith_minus_1" "10 - 5" "5";
    t "prim2_arith_minus_2" "-10000000000 - 1" "-10000000001";
    t "prim2_arith_times_1" "2 * 2" "4";
    t "prim2_arith_times_2" "-2 * 2" "-4";
    t "prim2_arith_times_3" "2 * -2" "-4";
    (* Exception checks *)
    terr "prim2_arith_plus_e_1" "1 + 4611686018427387903"
      "overflow occurred with value: -4611686018427387904";
    terr "prim2_arith_minus_e_1" "false - 5"
      "arithmetic expected a number, got: false";
    terr "prim2_arith_minus_e_2" "true - 1"
      "arithmetic expected a number, got: true";
    terr "prim2_arith_minus_e_3" "true - false"
      "arithmetic expected a number, got: true";
    terr "prim1_arith_minus_e_4" "-4611686018427387904 - 1"
      "overflow occurred with value: 4611686018427387903";
    terr "prim2_arith_minus_e_5" "0 - (-4611686018427387904)"
      "overflow occurred with value: -4611686018427387904";
    terr "prim2_arith_times_e_1" "true * 3"
      "arithmetic expected a number, got: true";
    terr "prim2_arith_times_e_2" "3 * false"
      "arithmetic expected a number, got: false";
    terr "prim2_arith_times_e_3" "true * false"
      "arithmetic expected a number, got: true" ]
;;

let prim2_comp_suite =
  [ t "prim2_comp_eq_1" "1 == 2" "false";
    t "prim2_comp_eq_2" "1 == 1" "true";
    t "prim2_comp_eq_3" "1 == false" "false";
    t "prim2_comp_eq_4" "true == true" "true";
    t "prim2_comp_eq_5" "true == false" "false";
    t "prim2_comp_eq_tup_0" "(3, 4) == (3, 4)" "false";
    t "prim2_comp_eq_tup_1" "let a = (3, 4) in a == a" "true";
    t "prim2_comp_g_1" "1 > 0" "true";
    t "prim2_comp_g_2" "1 > -5" "true";
    t "prim2_comp_g_3" "1 > 5" "false";
    t "prim2_comp_g_4" "1 > 1" "false";
    t "prim2_comp_g_5" "-4 > -4" "false";
    t "prim2_comp_g_6" "-4 > -8" "true";
    t "prim2_comp_g_7" "-8 > -4" "false";
    t "prim2_comp_ge_1" "1 >= 0" "true";
    t "prim2_comp_ge_2" "1 >= -5" "true";
    t "prim2_comp_ge_3" "1 >= 5" "false";
    t "prim2_comp_ge_4" "1 >= 1" "true";
    t "prim2_comp_ge_5" "-4 >= -4" "true";
    t "prim2_comp_ge_6" "-4 >= -8" "true";
    t "prim2_comp_ge_7" "-8 >= -4" "false";
    t "prim2_comp_l_1" "1 < 0" "false";
    t "prim2_comp_l_2" "1 < -5" "false";
    t "prim2_comp_l_3" "1 < 5" "true";
    t "prim2_comp_l_4" "1 < 1" "false";
    t "prim2_comp_l_5" "-4 < -4" "false";
    t "prim2_comp_l_6" "-4 < -8" "false";
    t "prim2_comp_l_7" "-8 < -4" "true";
    t "prim2_comp_le_1" "1 <= 0" "false";
    t "prim2_comp_le_2" "1 <= -5" "false";
    t "prim2_comp_le_3" "1 <= 5" "true";
    t "prim2_comp_le_4" "1 <= 1" "true";
    t "prim2_comp_le_5" "-4 <= -4" "true";
    t "prim2_comp_le_6" "-4 <= -8" "false";
    t "prim2_comp_le_7" "-8 <= -4" "true";
    (* Exception checks *)
    terr "prim2_comp_g_e_1" "false > 1"
      "comparison expected a number, got: false";
    terr "prim2_comp_g_e_2" "1 > true" "comparison expected a number, got: true";
    terr "prim2_comp_g_e_3" "false > true"
      "comparison expected a number, got: false";
    terr "prim2_comp_ge_e_1" "false >= 1"
      "comparison expected a number, got: false";
    terr "prim2_comp_ge_e_2" "1 >= true"
      "comparison expected a number, got: true";
    terr "prim2_comp_ge_e_3" "false >= true"
      "comparison expected a number, got: false";
    terr "prim2_comp_l_e_1" "false < 1"
      "comparison expected a number, got: false";
    terr "prim2_comp_l_e_2" "1 < true" "comparison expected a number, got: true";
    terr "prim2_comp_l_e_3" "false < true"
      "comparison expected a number, got: false";
    terr "prim2_comp_le_e_1" "false <= 1"
      "comparison expected a number, got: false";
    terr "prim2_comp_le_e_2" "1 <= true"
      "comparison expected a number, got: true";
    terr "prim2_comp_le_e_3" "false <= true"
      "comparison expected a number, got: false" ]
;;

(* There are more 'if' tests in the input_file_test_suite *)
let if_suite =
  [ t "if_1" "if true : add1(1) else: add1(2)" "2";
    t "if_2" "if false : add1(1) else: add1(2)" "3";
    t "if1" "if true: 4 else: 2" "4";
    t "if2" "if false: 4 else: 2" "2";
    t "if-bind-back" "if !(sub1(1) == 0) : 3 * 4 else: 0 + 3" "3";
    t "if-bind-front" "3 + (if !(sub1(1) == 0) : 3 * 4 else: 0)" "3";
    t "two-ifs" "if !(sub1(1) == 0) : 42 else: if true : 32 else: 56" "32";
    (* Exception checks *)
    terr "if_e_1" "if 4 : add1(1) else: add1(2)" "if expected a boolean, got: 4"
  ]
;;

let tuple_suite =
  [ t "tuple_nil" "nil" "nil";
    t "tuple_empty" "()" "()";
    t "tuple_one" "(false,)" "(false,)";
    t "tuple_two" "(3,8)" "(3, 8)";
    t "tuple_many" "(1,true,5,6,9,20,false,8)"
      "(1, true, 5, 6, 9, 20, false, 8)";
    terr "tuple_e_1" "4[0]" "expected a tuple, got: 4";
    terr "tuple_e_2" "(1,2)[-1]" "too low";
    terr "tuple_e_3" "(1,2)[3]" "too high";
    terr "tuple_e_4" "nil[0]" "attempt to dereference nil" ]
;;

let catch_all_suite =
  [terr "nothing" "" "ParseError(\"Parse error at line 1, col 0: token ``\")"]
;;

let out_of_memory_suite =
  [ tgcerr "oomgc1"
      (7 + (4 * List.length native_fun_env))
      "(1, (3, 4))" "out of memory";
    tgc "oomgc2"
      (8 + (4 * List.length native_fun_env))
      "(1, (3, 4))" "(1, (3, 4))";
    tvgc "oomgc3"
      (8 + (4 * List.length native_fun_env))
      "(1, (3, 4))" "(1, (3, 4))";
    tgc "oomgc4" (4 + (4 * List.length native_fun_env)) "(3, 4)" "(3, 4)" ]
;;

let input_suite =
  [ t "input1" "let x = input() in x + 2" ~input:"123" "125";
    t "input_print_true" "print(input())" ~input:"true" "true\ntrue";
    t "input_print_false" "print(input())" ~input:"false" "false\nfalse";
    t "input_print_pos_num" "print(input())" ~input:"3" "3\n3";
    t "input_print_neg_num" "print(input())" ~input:"-42" "-42\n-42";
    t "input_print_big_pos_num" "print(input())" ~input:"4611686018427387903"
      "4611686018427387903\n4611686018427387903";
    t "input_print_small_neg_num" "print(input())" ~input:"-4611686018427387904"
      "-4611686018427387904\n-4611686018427387904";
    t "input_garbage_whitespace" "print(input())" ~input:"   \n \n \n \n true"
      "true\ntrue";
    t "input_two_inputs_spaced"
      "let a = input(), b = input(), c = print(a) in b" ~input:"true false"
      "true\nfalse";
    t "input_two_inputs_spaced_newline"
      "let a = input(), b = input(), c = print(a) in b" ~input:" 5 13 \n"
      "5\n13";
    t "input_two_inputs_newlined"
      "let a = input(), b = input(), c = print(a) in b" ~input:"3\n-1353"
      "3\n-1353";
    t "input_add_two_nums" "input() + input()" ~input:"4\n2" "6";
    t "input_two_inputs_extra_inputs"
      "let a = input(), b = input(), c = print(a) in b" ~input:"1 2 3 4 5 6 7"
      "1\n2";
    terr "input_invalid_string" "input()" ~input:"hello" "Unknown input: hello";
    terr "input_invalid_no_input" "input()" ~input:"" "Ran out of input: EOF";
    terr "input_invalid_num_too_large" "input()" ~input:"4611686018427387904"
      "Integer input is out of range: 4611686018427387904";
    terr "input_invalid_num_too_small" "input()" ~input:"-4611686018427387905"
      "Integer input is out of range: -4611686018427387905";
    terr "input_invalid_num_way_too_big" "input()"
      ~input:"11111114611686018427387905"
      "Input failed: Numerical result out of range";
    terr "input_invalid_too_long" "input()"
      ~input:"1111111461161351235213521351233586018427387905"
      "Input does not fit into buffer";
    terr "input_invalid_tuple" "input()" ~input:"(3, 4)" "Unknown input: (3,";
    terr "input_wrong_arity_one" "input(true)" ~input:"false"
      "The function called at <input_wrong_arity_one, 1:0-1:11> expected an \
       arity of 0, but received 1 arguments" ]
;;

let print_suite =
  [ t "print_pos_num" "print(4)" "4\n4";
    t "print_neg_num" "print(-4)" "-4\n-4";
    t "print_true" "print(true)" "true\ntrue";
    t "print_false" "print(false)" "false\nfalse";
    t "print_twice" "print(print(13))" "13\n13\n13";
    t "print_expr" "let x = print(false) in print(!(x))" "false\ntrue\ntrue";
    t "print_large_num" "print(10000000000000000)"
      "10000000000000000\n10000000000000000";
    terr "print_wrong_arity_two" "print(3, (14, 15))"
      "The function called at <print_wrong_arity_two, 1:0-1:18> expected an \
       arity of 1, but received 2 arguments" ]
;;

let equal_suite =
  [ t "equal_bool_tt" "equal(true, true)" "true";
    t "equal_bool_tf" "equal(true, false)" "false";
    t "equal_bool_ft" "equal(false, true)" "false";
    t "equal_bool_ff" "equal(false, false)" "true";
    t "equal_bool_int" "equal(false, 352)" "false";
    t "equal_int_bool" "equal(-643, true)" "false";
    t "equal_bool_nil" "equal(true, nil)" "false";
    t "equal_nil_bool" "equal(nil, false)" "false";
    t "equal_bool_tuple" "equal(false, (1,3,false))" "false";
    t "equal_tuple_bool" "equal((), true)" "false";
    t "equal_int_eq" "equal(42, 42)" "true";
    t "equal_int_neq" "equal(-55, 15)" "false";
    t "equal_nil_nil" "equal(nil, nil)" "true";
    t "equal_tuple_eq_zero" "equal((), ())" "true";
    t "equal_tuple_eq_one" "equal((3,), (3,))" "true";
    t "equal_tuple_eq_two" "equal((1, false), (1, false))" "true";
    t "equal_tuple_eq_nest"
      "equal(((), 3, (14, 5, (8, 9, true, (10,)))), ((), 3, (14, 5, (8, 9, \
       true, (10,)))))"
      "true";
    t "equal_tuple_neq_size" "equal((1, 3), (1, 1, false))" "false";
    t "equal_tuple_neq_elem" "equal((1, false), (1, 4))" "false";
    terr "equal_wrong_arity_zero" "equal()"
      "The function called at <equal_wrong_arity_zero, 1:0-1:7> expected an \
       arity of 2, but received 0 arguments";
    terr "equal_wrong_arity_one" "equal((-42,))"
      "The function called at <equal_wrong_arity_one, 1:0-1:13> expected an \
       arity of 2, but received 1 arguments";
    terr "equal_wrong_arity_four" "equal(true, 3, (), 19)"
      "The function called at <equal_wrong_arity_four, 1:0-1:22> expected an \
       arity of 2, but received 4 arguments" ]
;;

let free_vars_suite =
  (* Basic sanity *)
  [ tfvs "fv_trivial_1" "4" [];
    tfvs "fv_1"
      "let x = 10 in let y = 12 in let f = (lambda(z): x + y + z) in f(5)" [];
    tfvs "fv_2" "let y = 12 in let f = (lambda(z): x + y + z) in f(5)" ["x"];
    tfvs "fv_3" "let f = (lambda(z): x + y + z) in f(5)" ["x"; "y"];
    tfvs "fv_4" "(lambda(z): let a = x in a + y + z)" ["x"; "y"];
    tfvs "fv_5" "let x = (lambda(m): let t = m in x + t) in x + y" ["x"; "y"];
    tfvs "fv_6" "(lambda(m): let t = m in x + t)" ["x"];
    tfvs "fv_7" "let y = y in y" ["y"];
    tfvs "fv_8" "let x = 5 in let l = (lambda: let x = x in x) in l()" [];
    tfvs "fv_9" "let l = (lambda: let x = x in x) in l()" ["x"];
    tfvs "fv_10"
      "(let rec x = (lambda (y): x(y)), a = (lambda (n): x(n)) in x(1))" [] ]
;;

let lambda_suite =
  [ t "lambda_print_no_args" "print((lambda:()))"
      "<closure, arity = 0, free_var_cnt = 0>\n\
       <closure, arity = 0, free_var_cnt = 0>";
    t "lambda_print_one_args" "print((lambda(x):x))"
      "<closure, arity = 1, free_var_cnt = 0>\n\
       <closure, arity = 1, free_var_cnt = 0>";
    t "lambda_one_args" "print((lambda(x):x))"
      "<closure, arity = 1, free_var_cnt = 0>\n\
       <closure, arity = 1, free_var_cnt = 0>";
    t "lambda_call_with_lambda" "(lambda(x):x)((lambda(a,b):a + b))"
      "<closure, arity = 2, free_var_cnt = 0>";
    t "lambda_curry_call" "((lambda(a): (lambda(b): a + b)))(5)(3)" "8" ]
;;

let suite =
  "suite"
  >::: naive_stack_allocation_suite @ collect_duplicates_suite @ enumerate_suite
       @ collect_arg_cycles_suite @ well_formedness_suite @ let_suite
       @ prim1_suite @ prim2_logic_suite @ prim2_arith_suite @ prim2_comp_suite
       @ if_suite @ catch_all_suite @ tuple_suite @ out_of_memory_suite
       @ input_suite @ print_suite @ equal_suite @ free_vars_suite
       @ lambda_suite
;;

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
