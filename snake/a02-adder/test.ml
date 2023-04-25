open Compile
open Sexp
open Runner
open Printf
open OUnit2
open ExtLib

(* Runs a program, given as a source string, and compares its output to
   expected *)
let t (name : string) (program : string) (expected : string) : OUnit2.test =
  name >:: test_run program name expected
;;

(* Runs a program, given as a source string, and compares its error to
   expected *)
let te (name : string) (program : string) (expected_err : string) : OUnit2.test
    =
  name >:: test_err program name expected_err
;;

(* Runs a program, given as the name of a file in the input/ directory, and
   compares its output to expected *)
let ti (filename : string) (expected : string) =
  filename >:: test_run_input filename expected
;;

(* Runs a program, given as the name of a file in the input/ directory, and
   compares its error to expected *)
let tie (filename : string) (expected_err : string) =
  filename >:: test_err_input filename expected_err
;;

(* a helper for testing primitive values (won't print datatypes well) *)
let t_expr (program : string) expected =
  program
  >:: fun _ ->
  assert_equal expected (expr_of_sexp (parse program)) ~printer:dump
;;

(* a helper for testing bad expressions *)
let t_expr_fail (program : string) expected =
  program
  >:: fun _ -> assert_raises expected (fun _ -> expr_of_sexp (parse program))
;;

(* a helper for testing strings *)
let t_string name (value : string) (expected : string) =
  name
  >:: fun _ -> assert_equal expected value ~printer:(fun s -> sprintf "%S" s)
;;

let expr_suite =
  [ t_expr "1" (Number (1L, (0, 0, 0, 1)));
    t_expr "(add1 0)" (Prim1 (Add1, Number (0L, (0, 6, 0, 7)), (0, 0, 0, 8)));
    t_expr "(sub1 (add1 (sub1 5)))"
      (Prim1
         ( Sub1,
           Prim1
             ( Add1,
               Prim1 (Sub1, Number (5L, (0, 18, 0, 19)), (0, 12, 0, 20)),
               (0, 6, 0, 21) ),
           (0, 0, 0, 22) ) );
    t_expr "(let ((x 10)) x)"
      (Let
         ( [("x", Number (10L, (0, 9, 0, 11)))],
           Id ("x", (0, 14, 0, 15)),
           (0, 0, 0, 16) ) );
    t_expr "(let ((x 10)) (add1 x))"
      (Let
         ( [("x", Number (10L, (0, 9, 0, 11)))],
           Prim1 (Add1, Id ("x", (0, 20, 0, 21)), (0, 14, 0, 22)),
           (0, 0, 0, 23) ) );
    t_expr "(let ((x 5) (y (sub1 x))) (sub1 y))"
      (Let
         ( [ ("x", Number (5L, (0, 9, 0, 10)));
             ("y", Prim1 (Sub1, Id ("x", (0, 21, 0, 22)), (0, 15, 0, 23))) ],
           Prim1 (Sub1, Id ("y", (0, 32, 0, 33)), (0, 26, 0, 34)),
           (0, 0, 0, 35) ) );
    t_expr_fail "3 3" (SexpParseFailure "Multiple top-level s-expressions found");
    t_expr_fail "let ((x (add1 3))) x)"
      (SexpParseFailure "Incomplete sexpression beginning at line 0, col 20");
    t_expr_fail "(let ((x (add1 3)) x)"
      (SexpParseFailure "Unmatched left paren at line 0, col 0");
    t_expr_fail "(let () 0)"
      (SyntaxError
         "'let' must contain at least one binding from line 0, col 5--line 0, \
          col 7" );
    t_expr_fail "true"
      (SyntaxError "Non-supported boolean value 'true' at line 0, col 0");
    t_expr_fail "false"
      (SyntaxError "Non-supported boolean value 'false' at line 0, col 0");
    t_expr_fail "(add1)"
      (SyntaxError
         "'add1' expression must have exactly one argument from line 0, col \
          0--line 0, col 6" );
    t_expr_fail "(sub1 3 4 (let ((x 10)) x))"
      (SyntaxError
         "'sub1' expression must have exactly one argument from line 0, col \
          0--line 0, col 27" );
    t_expr_fail "(let (3) 0)"
      (SyntaxError "Bindings should be within parentheses at line 0, col 6");
    t_expr_fail "(let ((x 5) true) 0)"
      (SyntaxError "Bindings should be within parentheses at line 0, col 12");
    t_expr_fail "(let ((x 5) (x 3)) x)"
      (SyntaxError
         "Name 'x' should not re-occur in 'let' bindings at line 0, col 13" );
    t_expr_fail "(let ((x 5) (y 1) (x 3)) y)"
      (SyntaxError
         "Name 'x' should not re-occur in 'let' bindings at line 0, col 19" );
    t_expr_fail "(let ((2 5)) 0)"
      (SyntaxError
         "Binding should contain only an identifier and an expression from \
          line 0, col 6--line 0, col 11" ) ]
;;

let asm_suite =
  [ t_string "RAX" (reg_to_asm_string RAX) "RAX";
    t_string "RSP" (reg_to_asm_string RSP) "RSP";
    t_string "arg RAX" (arg_to_asm_string (Reg RAX)) "RAX";
    t_string "arg RSP" (arg_to_asm_string (Reg RSP)) "RSP";
    t_string "arg 3" (arg_to_asm_string (Const 3L)) "3";
    t_string "arg 0" (arg_to_asm_string (Const 0L)) "0";
    t_string "arg -42" (arg_to_asm_string (Const (-42L))) "-42";
    t_string "arg -12345678"
      (arg_to_asm_string (Const (-12345678L)))
      "-12345678";
    t_string "arg 55555555" (arg_to_asm_string (Const 55555555L)) "55555555";
    t_string "arg [RAX]" (arg_to_asm_string (RegOffset (0, RAX))) "[RAX]";
    t_string "arg [RSP]" (arg_to_asm_string (RegOffset (0, RSP))) "[RSP]";
    t_string "arg [RSP + 8*1]"
      (arg_to_asm_string (RegOffset (1, RSP)))
      "[RSP + 8*1]";
    t_string "arg [RSP - 8*1]"
      (arg_to_asm_string (RegOffset (-1, RSP)))
      "[RSP - 8*1]";
    t_string "arg [RAX - 8*1]"
      (arg_to_asm_string (RegOffset (-1, RAX)))
      "[RAX - 8*1]";
    t_string "arg [RSP - 8*5]"
      (arg_to_asm_string (RegOffset (-5, RSP)))
      "[RSP - 8*5]";
    t_string "arg [RSP + 8*10]"
      (arg_to_asm_string (RegOffset (10, RSP)))
      "[RSP + 8*10]";
    t_string "arg [RAX + 8*12]"
      (arg_to_asm_string (RegOffset (12, RAX)))
      "[RAX + 8*12]";
    t_string "ret" (instruction_to_asm_string IRet) "\tret";
    t_string "mov RAX, RAX"
      (instruction_to_asm_string (IMov (Reg RAX, Reg RAX)))
      "\tmov RAX, RAX";
    t_string "mov RSP, RAX"
      (instruction_to_asm_string (IMov (Reg RSP, Reg RAX)))
      "\tmov RSP, RAX";
    t_string "mov RSP, 3"
      (instruction_to_asm_string (IMov (Reg RSP, Const 3L)))
      "\tmov RSP, 3";
    t_string "mov RAX, -4"
      (instruction_to_asm_string (IMov (Reg RAX, Const (-4L))))
      "\tmov RAX, -4";
    t_string "mov 2, 0"
      (instruction_to_asm_string (IMov (Const 2L, Const 0L)))
      "\tmov 2, 0";
    t_string "mov [RSP], 0"
      (instruction_to_asm_string (IMov (RegOffset (0, RSP), Const 0L)))
      "\tmov [RSP], 0";
    t_string "add RAX, [RAX + 8*4]"
      (instruction_to_asm_string (IAdd (Reg RAX, RegOffset (4, RAX))))
      "\tadd RAX, [RAX + 8*4]";
    t_string "add [RSP - 8*13], RAX"
      (instruction_to_asm_string (IAdd (RegOffset (-13, RSP), Reg RAX)))
      "\tadd [RSP - 8*13], RAX";
    t_string "add RSP, 3"
      (instruction_to_asm_string (IAdd (Reg RSP, Const 3L)))
      "\tadd RSP, 3";
    t_string "add RAX, -4"
      (instruction_to_asm_string (IAdd (Reg RAX, Const (-4L))))
      "\tadd RAX, -4";
    t_string "add 2, 0"
      (instruction_to_asm_string (IAdd (Const 2L, Const 0L)))
      "\tadd 2, 0";
    t_string "add [RSP], 0"
      (instruction_to_asm_string (IAdd (RegOffset (0, RSP), Const 0L)))
      "\tadd [RSP], 0";
    t_string "(let ((x 10)) x)"
      (to_asm_string
         [ IMov (Reg RAX, Const 10L);
           IMov (RegOffset (~-1, RSP), Reg RAX);
           IMov (Reg RAX, RegOffset (~-1, RSP));
           IAdd (Reg RAX, Const 1L) ] )
      "\n\
       \tmov RAX, 10\n\
       \tmov [RSP - 8*1], RAX\n\
       \tmov RAX, [RSP - 8*1]\n\
       \tadd RAX, 1";
    t_string "positive offset, not possible in actual Adder program"
      (to_asm_string
         [ IMov (Reg RAX, Const 10L);
           IMov (RegOffset (1, RSP), Reg RAX);
           IMov (Reg RAX, RegOffset (1, RSP));
           IAdd (Reg RAX, Const 1L) ] )
      "\n\
       \tmov RAX, 10\n\
       \tmov [RSP + 8*1], RAX\n\
       \tmov RAX, [RSP + 8*1]\n\
       \tadd RAX, 1";
    t_string "instructions with a return"
      (to_asm_string
         [ IMov (Reg RAX, Const (-3L));
           IAdd (Reg RAX, Const 42L);
           IAdd (Reg RAX, Reg RSP);
           IMov (RegOffset (3, RSP), Reg RAX);
           IRet ] )
      "\n\
       \tmov RAX, -3\n\
       \tadd RAX, 42\n\
       \tadd RAX, RSP\n\
       \tmov [RSP + 8*3], RAX\n\
       \tret" ]
;;

let program_suite =
  [ (* Test successful compile *)
    t "number-1" "1" "1";
    t "add1-0" "(add1 0)" "1";
    t "sub1-add1-sub1-5" "(sub1 (add1 (sub1 5)))" "4";
    t "let-x-10-x" "(let ((x 10)) x)" "10";
    t "let-add1-10-add1" "(let ((add1 10)) add1)" "10";
    t "let-let-3-add1-add1-let-let" "(let ((let 3) (add1 (add1 let))) let)" "3";
    t "let-a-3-let-b-sub1-a-add1-let-c-add1-a-b"
      "(let ((a 3)) (let ((b (sub1 a))) (add1 (let ((c (add1 a))) b))))" "3";
    t "let-x-5-add1-x" "(let ((x 5)) (add1 x))" "6";
    t "let-x-5-y-sub1-x-sub1-y" "(let ((x 5) (y (sub1 x))) (sub1 y))" "3";
    (* Test failed compile *)
    te "missing-l-paren" "let ((x (add1 3))) x)"
      "Sexp.SexpParseFailure(\"Incomplete sexpression beginning at line 0, col \
       20\")";
    te "missing-r-paren" "(let ((x (add1 3)) x)"
      "Sexp.SexpParseFailure(\"Unmatched left paren at line 0, col 0\")";
    te "let-x-3-y" "(let ((x 3)) y)"
      "Compile.BindingError(\"Unknown variable 'y' at line 0, col 13\")";
    (* Test successful compile from files *)
    ti "test1.adder" "2";
    ti "test2.adder" "12";
    ti "test3.adder" "9";
    ti "test4.adder" "6";
    (* Test failed compile from files *)
    tie "fail1.adder"
      "Compile.BindingError(\"Unknown variable 'x' at line 0, col 6\")";
    tie "fail2.adder"
      "Compile.BindingError(\"Unknown variable 'z' at line 1, col 9\")";
    tie "fail3.adder"
      "Compile.BindingError(\"Unknown variable 'j' at line 5, col 25\")";
    tie "fail4.adder"
      "Compile.BindingError(\"Unknown variable 'z' at line 7, col 33\")" ]
;;

let suite : OUnit2.test = "suite" >::: expr_suite @ asm_suite @ program_suite

let () = run_test_tt_main suite
