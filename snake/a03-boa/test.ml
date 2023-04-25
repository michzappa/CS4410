open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open ExtLib

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

(* Tags a string program and compares the output to expected *)
let ttags (name : string) (program : string) (expected : tag expr) =
  name
  >:: fun _ ->
  let parsed = parse_string name program in
  let result = check_scope parsed; parsed |> tag in
  assert_equal expected result ~printer:string_of_expr
;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf (name : string) (program : 'a expr) (expected : unit expr) =
  name
  >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_expr
;;

(* Transforms a string program into ANF, and compares the output to expected *)
let tanfs (name : string) (program : string) (expected : unit expr) =
  name
  >:: fun _ ->
  let parsed = parse_string name program in
  let check =
    check_scope parsed;
    parsed |> tag |> rename |> anf
  in
  assert_equal expected check ~printer:string_of_expr
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

let check_scope_suite =
  [ te "bad_scope_00" "val"
      "Compile.BindingError(\"Unbound identifier 'val' at bad_scope_00, \
       1:0-1:3\")";
    te "bad_scope_01" "let x = 1, y = z, z = x in z"
      "Compile.BindingError(\"Unbound identifier 'z' at bad_scope_01, \
       1:15-1:16\")";
    te "bad_scope_02" "let x = 1, z = x, x = z in z"
      "Compile.BindingError(\"Repeat name 'x' in binding at bad_scope_02, \
       1:18-1:23\")";
    te "bad_scope_03" "if 0 :\n  let y = 3 in y\nelse:\n  let x = 2 in y"
      "Compile.BindingError(\"Unbound identifier 'y' at bad_scope_03, \
       4:15-4:16\")";
    te "bad_scope_04" "if x : 0 else: 0"
      "Compile.BindingError(\"Unbound identifier 'x' at bad_scope_04, \
       1:3-1:4\")";
    te "bad_scope_05" "if 0 : x else: 0"
      "Compile.BindingError(\"Unbound identifier 'x' at bad_scope_05, \
       1:7-1:8\")";
    te "bad_scope_06" "if 0 : 0 else: x"
      "Compile.BindingError(\"Unbound identifier 'x' at bad_scope_06, \
       1:15-1:16\")";
    te "bad_scope_07" "add1(z)"
      "Compile.BindingError(\"Unbound identifier 'z' at bad_scope_07, \
       1:5-1:6\")";
    te "bad_scope_08" "sub1(t)"
      "Compile.BindingError(\"Unbound identifier 't' at bad_scope_08, \
       1:5-1:6\")";
    te "bad_scope_09" "add1(sub1(t))"
      "Compile.BindingError(\"Unbound identifier 't' at bad_scope_09, \
       1:10-1:11\")";
    te "bad_scope_10" "sub1(add1(t))"
      "Compile.BindingError(\"Unbound identifier 't' at bad_scope_10, \
       1:10-1:11\")";
    te "bad_scope_11" "k + 0"
      "Compile.BindingError(\"Unbound identifier 'k' at bad_scope_11, \
       1:0-1:1\")";
    te "bad_scope_12" "0 + k"
      "Compile.BindingError(\"Unbound identifier 'k' at bad_scope_12, \
       1:4-1:5\")";
    te "bad_scope_13" "k + t"
      "Compile.BindingError(\"Unbound identifier 'k' at bad_scope_13, \
       1:0-1:1\")";
    te "bad_scope_14" "k - 0"
      "Compile.BindingError(\"Unbound identifier 'k' at bad_scope_14, \
       1:0-1:1\")";
    te "bad_scope_15" "0 - k"
      "Compile.BindingError(\"Unbound identifier 'k' at bad_scope_15, \
       1:4-1:5\")";
    te "bad_scope_16" "k - t"
      "Compile.BindingError(\"Unbound identifier 'k' at bad_scope_16, \
       1:0-1:1\")";
    te "bad_scope_17" "k * 0"
      "Compile.BindingError(\"Unbound identifier 'k' at bad_scope_17, \
       1:0-1:1\")";
    te "bad_scope_18" "0 * k"
      "Compile.BindingError(\"Unbound identifier 'k' at bad_scope_18, \
       1:4-1:5\")";
    te "bad_scope_19" "k * t"
      "Compile.BindingError(\"Unbound identifier 'k' at bad_scope_19, \
       1:0-1:1\")";
    te "bad_scope_20" "(v)"
      "Compile.BindingError(\"Unbound identifier 'v' at bad_scope_20, \
       1:1-1:2\")";
    te "bad_scope_21" "(((((((v)))))))"
      "Compile.BindingError(\"Unbound identifier 'v' at bad_scope_21, \
       1:7-1:8\")";
    te "bad_scope_21" "let y = 0, x = 1, z = 2, x = 3, z = 4 in z"
      "Compile.BindingError(\"Repeat name 'x' in binding at bad_scope_21, \
       1:25-1:30\")" ]
;;

let tag_suite =
  [ ttags "tag_str_01" "41" (ENumber (41L, 1));
    ttags "tag_str_02" "sub1(41)" (EPrim1 (Sub1, ENumber (41L, 1), 2));
    ttags "tag_str_03" "let x = 41 in x"
      (ELet ([("x", ENumber (41L, 1), 2)], EId ("x", 3), 4));
    ttags "tag_str_04" "let x = 41, y = x + 2 in y - 5"
      (ELet
         ( [ ("x", ENumber (41L, 1), 2);
             ("y", EPrim2 (Plus, EId ("x", 3), ENumber (2L, 4), 5), 6) ],
           EPrim2 (Minus, EId ("y", 7), ENumber (5L, 8), 9),
           10 ) );
    ttags "tag_str_04" "let x = 3, y = 2, z = x * y in if x : y + z else: z - y"
      (ELet
         ( [ ("x", ENumber (3L, 1), 2);
             ("y", ENumber (2L, 3), 4);
             ("z", EPrim2 (Times, EId ("x", 5), EId ("y", 6), 7), 8) ],
           EIf
             ( EId ("x", 9),
               EPrim2 (Plus, EId ("y", 10), EId ("z", 11), 12),
               EPrim2 (Minus, EId ("z", 13), EId ("y", 14), 15),
               16 ),
           17 ) ) ]
;;

let anf_suite =
  [ tanf "forty_one_anf" (ENumber (41L, ())) (ENumber (41L, ()));
    (* For CS4410 students, with unnecessary let-bindings *)
    (* tanf "prim1_anf_4410"
         (EPrim1 (Sub1, ENumber (55L, ()), ()))
         (ELet
            ( [("$prim1_2", EPrim1 (Sub1, ENumber (55L, ()), ()), ())],
              EId ("$prim1_2", ()),
              () ) );
       tanfs "prim1_anf_4410_str" "sub1(55)"
         (ELet
            ( [("$prim1_2", EPrim1 (Sub1, ENumber (55L, ()), ()), ())],
              EId ("$prim1_2", ()),
              () ) ); *)
    (* For CS6410 students, with optimized let-bindings *)
    tanf "prim1_anf_6410"
      (EPrim1 (Sub1, ENumber (55L, ()), ()))
      (EPrim1 (Sub1, ENumber (55L, ()), ()));
    ta "forty_one_run_anf" (tag (ENumber (41L, ()))) "41";
    (* Our own tests *)
    tanfs "anf_str_01" "sub1(add1(3))"
      (ELet
         ( [("$prim1_2", EPrim1 (Add1, ENumber (3L, ()), ()), ())],
           EPrim1 (Sub1, EId ("$prim1_2", ()), ()),
           () ) );
    tanfs "anf_str_02" "3 + 2"
      (EPrim2 (Plus, ENumber (3L, ()), ENumber (2L, ()), ()));
    tanfs "anf_str_03" "(1 + 4) + 2"
      (ELet
         ( [ ( "$prim2_3",
               EPrim2 (Plus, ENumber (1L, ()), ENumber (4L, ()), ()),
               () ) ],
           EPrim2 (Plus, EId ("$prim2_3", ()), ENumber (2L, ()), ()),
           () ) );
    tanfs "anf_str_04" "(1 + 4) * (3 - 2)"
      (ELet
         ( [ ( "$prim2_3",
               EPrim2 (Plus, ENumber (1L, ()), ENumber (4L, ()), ()),
               () ) ],
           ELet
             ( [ ( "$prim2_6",
                   EPrim2 (Minus, ENumber (3L, ()), ENumber (2L, ()), ()),
                   () ) ],
               EPrim2 (Times, EId ("$prim2_3", ()), EId ("$prim2_6", ()), ()),
               () ),
           () ) );
    tanfs "anf_str_05" "3 * (1 + 4)"
      (ELet
         ( [ ( "$prim2_4",
               EPrim2 (Plus, ENumber (1L, ()), ENumber (4L, ()), ()),
               () ) ],
           EPrim2 (Times, ENumber (3L, ()), EId ("$prim2_4", ()), ()),
           () ) );
    tanfs "anf_str_06" "23" (ENumber (23L, ()));
    tanfs "anf_str_07" "let x = 2 in x"
      (ELet ([("x#2", ENumber (2L, ()), ())], EId ("x#2", ()), ()));
    tanfs "anf_str_08" "let x = 2 in let y = x in y"
      (ELet
         ( [("x#2", ENumber (2L, ()), ())],
           ELet ([("y#4", EId ("x#2", ()), ())], EId ("y#4", ()), ()),
           () ) );
    tanfs "anf_str_09" "let x = (let y = 2 in y) in x"
      (ELet
         ( [ ( "x#5",
               ELet ([("y#2", ENumber (2L, ()), ())], EId ("y#2", ()), ()),
               () ) ],
           EId ("x#5", ()),
           () ) );
    tanfs "anf_str_10" "if 0 : 1 else: 2"
      (EIf (ENumber (0L, ()), ENumber (1L, ()), ENumber (2L, ()), ()));
    tanfs "anf_str_11" "add1(if 0 : 1 else: 2)"
      (ELet
         ( [ ( "$if_4",
               EIf (ENumber (0L, ()), ENumber (1L, ()), ENumber (2L, ()), ()),
               () ) ],
           EPrim1 (Add1, EId ("$if_4", ()), ()),
           () ) );
    tanfs "anf_str_12" "let x = 2, y = x, z = y in z"
      (ELet
         ( [("x#2", ENumber (2L, ()), ())],
           ELet
             ( [("y#4", EId ("x#2", ()), ())],
               ELet ([("z#6", EId ("y#4", ()), ())], EId ("z#6", ()), ()),
               () ),
           () ) );
    tanfs "anf_str_13" "let x = 2, y = (let x = x in x), z = y in z"
      (ELet
         ( [("x#2", ENumber (2L, ()), ())],
           ELet
             ( [ ( "y#7",
                   ELet ([("x#4", EId ("x#2", ()), ())], EId ("x#4", ()), ()),
                   () ) ],
               ELet ([("z#9", EId ("y#7", ()), ())], EId ("z#9", ()), ()),
               () ),
           () ) );
    tanfs "anf_str_14" "sub1(if 0 : add1(1) else: add1(2))"
      (ELet
         ( [ ( "$if_6",
               EIf
                 ( ENumber (0L, ()),
                   EPrim1 (Add1, ENumber (1L, ()), ()),
                   EPrim1 (Add1, ENumber (2L, ()), ()),
                   () ),
               () ) ],
           EPrim1 (Sub1, EId ("$if_6", ()), ()),
           () ) );
    tanfs "anf_str_15" "sub1(if 0 : add1(3+1) else: add1(2))"
      (ELet
         ( [ ( "$if_8",
               EIf
                 ( ENumber (0L, ()),
                   ELet
                     ( [ ( "$prim2_4",
                           EPrim2 (Plus, ENumber (3L, ()), ENumber (1L, ()), ()),
                           () ) ],
                       EPrim1 (Add1, EId ("$prim2_4", ()), ()),
                       () ),
                   EPrim1 (Add1, ENumber (2L, ()), ()),
                   () ),
               () ) ],
           EPrim1 (Sub1, EId ("$if_8", ()), ()),
           () ) ) ]
;;

let program_suite =
  [ t "if1" "if 5: 4 else: 2" "4";
    t "if2" "if 0: 4 else: 2" "2";
    t "forty_one" "41" "41";
    t "letx2" "let x = 2 in x" "2";
    t "many_adds" "1+2+3+4+5+6" "21";
    t "many_adds_then_neg" "1+2+3+4+5+-6" "9";
    t "many_prim2s" "1 + 2 * 3 - 4 + 5" "10";
    t "1sub5" "1 - 5" "-4";
    t "if-bind-back" "if sub1(1) : 3 * 4 else: 0 + 3" "3";
    t "if-bind-front" "3 + (if sub1(1) : 3 * 4 else: 0)" "3";
    t "two-ifs" "if sub1(1) : 42 else: if 1 : 32 else: 56" "32";
    te "nothing" ""
      "Runner.ParseError(\"Parse error at line 1, col 0: token ``\")";
    (* Complete compile file tests *)
    tprog "test1.boa" "3";
    tprog "test2.boa" "-24";
    tprog "test3.boa" "1234";
    tprog "test4.boa" "20";
    tprog "test5.boa" "81";
    tprog "test6.boa" "189";
    tprog "test7.boa" "1870";
    tprog "test8.boa" "189";
    tprog "test9.boa" "56";
    tprog "test10.boa" "89";
    tprog "test11.boa" "126";
    tprog "test12.boa" "666";
    (* Fail compile file tests *)
    teprog "fail1.boa"
      "Compile.BindingError(\"Unbound identifier 'w' at fail1.boa, 5:16-5:17\")";
    teprog "fail2.boa"
      "Runner.ParseError(\"Parse error at line 1, col 10: token `in`\")";
    teprog "fail3.boa"
      "Compile.BindingError(\"Repeat name 'x' in binding at fail3.boa, \
       18:22-18:27\")";
    teprog "fail4.boa"
      "Runner.ParseError(\"Parse error at line 1, col 16: token ``\")";
    teprog "fail5.boa"
      "Compile.BindingError(\"Unbound identifier 'f' at fail5.boa, 6:31-6:32\")";
    teprog "fail6.boa" "Failure(\"Int64.of_string\")";
    teprog "fail7.boa"
      "Compile.BindingError(\"Unbound identifier 'x' at fail7.boa, 2:4-2:5\")";
    teprog "fail8.boa"
      "Compile.BindingError(\"Unbound identifier 'a' at fail8.boa, 3:12-3:13\")";
    teprog "fail9.boa"
      "Compile.BindingError(\"Repeat name 'x' in binding at fail9.boa, \
       7:16-7:22\")";
    teprog "fail10.boa"
      "Compile.BindingError(\"Repeat name 'z' in binding at fail10.boa, \
       3:15-3:20\")" ]
;;

let suite =
  "suite" >::: check_scope_suite @ tag_suite @ anf_suite @ program_suite
;;

let () = run_test_tt_main suite
