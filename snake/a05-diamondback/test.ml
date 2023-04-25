open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Utils

let t_any name value expected =
  name >:: fun _ -> assert_equal expected value ~printer:ExtLib.dump
;;

let t name program expected = name >:: test_run program name expected

let ta name program_and_env expected =
  name >:: test_run_anf program_and_env name expected
;;

let te name program expected_err = name >:: test_err program name expected_err

let tvg name program expected = name >:: test_run_valgrind program name expected

let tanf name program expected =
  name
  >:: fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

let teq name actual expected =
  name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)
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
  [ (let ast = AProgram ([], ACExpr (CImmExpr (ImmNum (1L, 1))), 0) in
     t_any "sa_empty_program" (naive_stack_allocation ast) (ast, []) );
    (let ast =
       AProgram
         ( [],
           ALet
             ( "x",
               CImmExpr (ImmNum (1L, 1)),
               ACExpr (CImmExpr (ImmNum (1L, 2))),
               1 ),
           0 )
     in
     t_any "sa_no_decls_let_1"
       (naive_stack_allocation ast)
       (ast, [("x", RegOffset (~-8, RBP))]) );
    (let ast =
       AProgram
         ( [],
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
           0 )
     in
     t_any "sa_no_decls_let_2"
       (naive_stack_allocation ast)
       ( ast,
         [ ("x", RegOffset (~-8, RBP));
           ("y", RegOffset (~-16, RBP));
           ("z", RegOffset (~-24, RBP)) ] ) );
    (let ast =
       AProgram
         ( [ ADFun
               ( "f",
                 ["farg1"; "farg2"; "farg3"],
                 ACExpr (CImmExpr (ImmNum (1L, 9))),
                 8 ) ],
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
           0 )
     in
     t_any "sa_one_decls_let"
       (naive_stack_allocation ast)
       ( ast,
         [ ("farg1", RegOffset (16, RBP));
           ("farg2", RegOffset (24, RBP));
           ("farg3", RegOffset (32, RBP));
           ("x", RegOffset (~-8, RBP));
           ("y", RegOffset (~-16, RBP));
           ("z", RegOffset (~-24, RBP)) ] ) );
    (let ast =
       AProgram
         ( [ ADFun
               ( "f",
                 ["farg1"; "farg2"; "farg3"],
                 ACExpr (CImmExpr (ImmNum (1L, 9))),
                 8 );
             ADFun
               ( "g",
                 ["garg1"; "garg2"; "garg3"],
                 ACExpr (CImmExpr (ImmNum (1L, 10))),
                 11 ) ],
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
           0 )
     in
     t_any "sa_two_decls"
       (naive_stack_allocation ast)
       ( ast,
         [ ("farg1", RegOffset (16, RBP));
           ("farg2", RegOffset (24, RBP));
           ("farg3", RegOffset (32, RBP));
           ("garg1", RegOffset (16, RBP));
           ("garg2", RegOffset (24, RBP));
           ("garg3", RegOffset (32, RBP));
           ("x", RegOffset (~-8, RBP));
           ("y", RegOffset (~-16, RBP));
           ("z", RegOffset (~-24, RBP)) ] ) ) ]
;;

let well_formedness_suite =
  [ (* Ensure all detectable errors are printed *)
    te "wf_unbound_id_plus_1" "a + b" "The identifier a";
    te "wf_unbound_id_plus_2" "a + b" "The identifier b";
    te "wf_duplicate_id_let_1" "let x = 3, x = 4 in y + z" "The identifier x";
    te "wf_unbound_id_let_plus_1" "let x = 3, x = 4 in y + z" "The identifier y";
    te "wf_unbound_id_let_plus_2" "let x = 3, x = 4 in y + z" "The identifier z"
  ]
;;

(* TODO potentiall move these tests into the input file system, but first rename those that exist there already *)

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
    t "prim1_9" "print(4)" "4\n4";
    t "prim1_10" "print(-4)" "-4\n-4";
    t "prim1_11" "print(true)" "true\ntrue";
    t "prim1_12" "print(false)" "false\nfalse";
    t "prim1_13" "print(print(13))" "13\n13\n13";
    t "prim1_14" "let x = print(false) in print(!(x))" "false\ntrue\ntrue";
    t "prim1_15" "print(10000000000000000)"
      "10000000000000000\n10000000000000000";
    (* Exception checks *)
    te "prim1_e_1" "!(4)" "logic expected a boolean, got: 4";
    te "prim1_e_2" "add1(true)" "arithmetic expected a number, got: true";
    te "prim1_e_3" "sub1(false)" "arithmetic expected a number, got: false";
    te "prim1_e_4" "add1(4611686018427387903)" "overflow occurred";
    te "prim1_e_5" "sub1(-4611686018427387904)" "overflow occurred" ]
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
    te "prim2_logic_or_e_1" "4 || true" "logic expected a boolean, got: 4";
    te "prim2_logic_or_e_2" "false || 4" "logic expected a boolean, got: 4";
    te "prim2_logic_or_e_3" "1 || 4" "logic expected a boolean, got: 1";
    te "prim2_logic_and_e_1" "4 && true" "logic expected a boolean, got: 4";
    te "prim2_logic_and_e_2" "true && 4" "logic expected a boolean, got: 4";
    te "prim2_logic_and_e_3" "1 && 4" "logic expected a boolean, got: 1";
    te "prim2_arith_add_e_1" "true + 1"
      "arithmetic expected a number, got: true";
    te "prim2_arith_add_e_2" "1 + true"
      "arithmetic expected a number, got: true";
    te "prim2_arith_add_e_3" "true + false"
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
    te "prim2_arith_plus_e_1" "1 + 4611686018427387903"
      "overflow occurred with value: -4611686018427387904";
    te "prim2_arith_minus_e_1" "false - 5"
      "arithmetic expected a number, got: false";
    te "prim2_arith_minus_e_2" "true - 1"
      "arithmetic expected a number, got: true";
    te "prim2_arith_minus_e_3" "true - false"
      "arithmetic expected a number, got: true";
    te "prim1_arith_minus_e_4" "-4611686018427387904 - 1"
      "overflow occurred with value: 4611686018427387903";
    te "prim2_arith_minus_e_5" "0 - (-4611686018427387904)"
      "overflow occurred with value: -4611686018427387904";
    te "prim2_arith_times_e_1" "true * 3"
      "arithmetic expected a number, got: true";
    te "prim2_arith_times_e_2" "3 * false"
      "arithmetic expected a number, got: false";
    te "prim2_arith_times_e_3" "true * false"
      "arithmetic expected a number, got: true" ]
;;

let prim2_comp_suite =
  [ t "prim2_comp_eq_1" "1 == 2" "false";
    t "prim2_comp_eq_2" "1 == 1" "true";
    t "prim2_comp_eq_3" "1 == false" "false";
    t "prim2_comp_eq_4" "true == true" "true";
    t "prim2_comp_eq_5" "true == false" "false";
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
    te "prim2_comp_g_e_1" "false > 1" "comparison expected a number, got: false";
    te "prim2_comp_g_e_2" "1 > true" "comparison expected a number, got: true";
    te "prim2_comp_g_e_3" "false > true"
      "comparison expected a number, got: false";
    te "prim2_comp_ge_e_1" "false >= 1"
      "comparison expected a number, got: false";
    te "prim2_comp_ge_e_2" "1 >= true" "comparison expected a number, got: true";
    te "prim2_comp_ge_e_3" "false >= true"
      "comparison expected a number, got: false";
    te "prim2_comp_l_e_1" "false < 1" "comparison expected a number, got: false";
    te "prim2_comp_l_e_2" "1 < true" "comparison expected a number, got: true";
    te "prim2_comp_l_e_3" "false < true"
      "comparison expected a number, got: false";
    te "prim2_comp_le_e_1" "false <= 1"
      "comparison expected a number, got: false";
    te "prim2_comp_le_e_2" "1 <= true" "comparison expected a number, got: true";
    te "prim2_comp_le_e_3" "false <= true"
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
    te "if_e_1" "if 4 : add1(1) else: add1(2)" "if expected a boolean, got: 4"
  ]
;;

let catch_all_suite =
  [te "nothing" "" "ParseError(\"Parse error at line 1, col 0: token ``\")"]
;;

let suite =
  "unit_tests"
  >::: collect_duplicates_suite @ enumerate_suite @ collect_arg_cycles_suite
       @ naive_stack_allocation_suite @ well_formedness_suite @ let_suite
       @ prim1_suite @ prim2_logic_suite @ prim2_arith_suite @ prim2_comp_suite
       @ if_suite @ catch_all_suite
;;

(* input_file_test_suite () will run all the tests in the subdirectories of input/ *)
let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
