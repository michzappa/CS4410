open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs

(* A helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected =
  name >:: fun _ -> assert_equal expected value ~printer:ExtLib.dump
;;

(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) =
  name >:: test_run program name expected
;;

(* Runs a program, given as an ANFed expr, and compares its output to expected *)
let ta (name : string) (program : tag expr) (expected : string) =
  name >:: test_run_anf program name expected
;;

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) =
  name >:: test_err program name expected_err
;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf (name : string) (program : 'a expr) (expected : unit expr) =
  name
  >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_expr
;;

(* Checks if two strings are equal *)
let teq (name : string) (actual : string) (expected : string) =
  name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)
;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) =
  filename >:: test_run_input filename expected
;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) =
  filename >:: test_err_input filename expected
;;

let util_suite =
  [ t_any "err_concat_0" (Phases.err_concat []) (Ok []);
    t_any "err_concat_1" (Phases.err_concat [Ok ()]) (Ok [()]);
    t_any "err_concat_2"
      (Phases.err_concat [Ok (); Ok (); Ok (); Ok ()])
      (Ok [(); (); (); ()]);
    t_any "err_concat_3"
      (Phases.err_concat [Error [Failure "1"]])
      (Error [Failure "1"]);
    t_any "err_concat_4"
      (Phases.err_concat
         [Error [Failure "1"; Failure "2"]; Error [Failure "3"]] )
      (Error [Failure "1"; Failure "2"; Failure "3"]);
    t_any "err_concat_5"
      (Phases.err_concat
         [ Ok ();
           Error [Failure "1"; Failure "2"];
           Ok ();
           Error [Failure "3"];
           Ok () ] )
      (Error [Failure "1"; Failure "2"; Failure "3"]);
    (* Ensure all detectable errors are printed *)
    te "err_concat_6" "a + b" "The identifier a";
    te "err_concat_7" "a + b" "The identifier b";
    te "err_concat_8" "let x = 3, x = 4 in y + z" "The identifier x";
    te "err_concat_9" "let x = 3, x = 4 in y + z" "The identifier y";
    te "err_concat_10" "let x = 3, x = 4 in y + z" "The identifier z" ]
;;

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
  >::: util_suite @ let_suite @ prim1_suite @ prim2_logic_suite
       @ prim2_arith_suite @ prim2_comp_suite @ if_suite @ catch_all_suite
;;

(* input_file_test_suite () will run all the tests in the subdirectories of input/ *)
let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
