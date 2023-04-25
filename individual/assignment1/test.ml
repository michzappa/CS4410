open Sexp2
open OUnit2
open Expr
open ExtLib
open Printf

(* a helper for testing integers *)
let t_int name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:string_of_int);;

(* a helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:dump);;

(* Feel free to add any new testing functions you may need *)

(* a helper for testing failwith scenarios *)
let t_failure name thunk failure_message = name>::
  (fun _ -> assert_raises (Failure failure_message) thunk)

(* a helper for testing strings *)
let t_string name (value : string) (expected : string) =
  name >:: fun _ ->
           assert_equal expected value ~printer:(fun s -> sprintf "%S" s)

(* It can be useful to aggregate tests into lists if they test separate
functions, and put them together at the end *)

let env1 = [("a", 5); ("b", 15)];;

let get_tests = [
    t_any "get a" (get env1 "a") (Some(5));
    t_any "get b" (get env1 "b") (Some(15));
    t_any "get c" (get env1 "c") None;
    t_any "get c after adding" (get (add env1 "c" (-2)) "c") (Some(-2));
    t_any "get a after updating" (get (add env1 "a" 49) "a") (Some(49));
];;


let contains_tests = [
    t_any "contains a" (contains env1 "a") true;
    t_any "contains A" (contains env1 "A") false;
    t_any "contains b" (contains env1 "b") true;
    t_any "contains c" (contains env1 "c") false;
    t_any "contains \"\"" (contains env1 "") false;
    t_any "contains c after adding" (contains (add env1 "c" (-2)) "c") true;
    t_any "contains c after adding twice (duh)" (contains (add (add env1 "c" (-2)) "c" 0) "c") true;
];;

let add_tests = [
    t_any "env1 after adding c" (add env1 "c" (-2)) [("a", 5); ("b", 15); ("c", (-2))];
    t_any "env1 after updating a, no dups" (add env1 "a" 49) [("a", 49); ("b", 15)];
    t_any "adding same var repeatedly to empty env" (add (add (add [] "a" 1) "a" 2) "a" 3) [("a", 3)]
    (* integration tests for add in get_tests and contains_tests *)
];;

let evaluate_tests = [
  t_int "evaluate1" (evaluate (Times(Num(0), Num(5))) []) 0;
  t_int "evaluate2" (evaluate (Times(Num(1), Num(5))) []) 5;
  t_int "evaluate3" (evaluate (Variable("a")) env1) 5;
  t_int "evaluate4" (evaluate (Times(Variable("a"), Variable("b"))) env1) 75;
  t_int "evaluate5" (evaluate (Plus(Variable("a"), Variable("b"))) env1) 20;
  t_int "evaluate6" (evaluate (Plus(Num(23), Num(-6))) []) 17;
  t_int "evaluate7" (evaluate (Plus(Plus(Times(Plus(Num(5), Variable("a")), Variable("b")), Num(2)), Num(1))) env1)
    153;
  t_failure "evaluate failure 1" (fun _ -> (evaluate (Variable("a")) [])) "variable \"a\" not found";
  t_failure "evaluate failure 2" (fun _ -> (evaluate (Plus(Variable("c"), Num(0))) env1)) "variable \"c\" not found";
];;

let pretty_tests = [
    t_string "pretty value" (pretty (Num(5))) "5";
    t_string "pretty negative value" (pretty (Num(-5))) "-5";
    t_string "pretty variable" (pretty (Variable("var"))) "var";
    t_string "pretty plus" (pretty (Plus(Num(23), Num(-6)))) "23 + -6";
    t_string "pretty var coef 1" (pretty (Times(Variable("a"), Variable("b")))) "a * b";
    t_string "pretty var coef 2" (pretty (Times(Plus(Variable("a"), Num(4)), Variable("b"))))
      "(a + 4)b";
    t_string "pretty var coef 3" (pretty (Times(Times(Num(1), Num(2)), Variable("b"))))
      "(1 * 2)b";
    t_string "pretty pemdas 1" (pretty (Times(Plus(Num(1), Num(2)), Variable("b"))))
      "(1 + 2)b";
    t_string "pretty pemdas 2" (pretty (Times(Plus(Num(1), Num(2)), Plus(Num(3), Num(4)))))
      "(1 + 2) * (3 + 4)";
    t_string "pretty pemdas 3" (pretty (Times(Plus(Num(1), Num(2)), Plus(Times(Variable("a"), Num(6)), Num(4)))))
      "(1 + 2) * (a * 6 + 4)";
    t_string "pretty pemdas 4" (pretty (Times(Times(Num(1), Num(2)), Plus(Times(Variable("a"), Num(6)), Num(4)))))
      "1 * 2 * (a * 6 + 4)";
    t_string "pretty no parens 1" (pretty (Plus(Plus(Num(1), Num(2)), Variable("b"))))
      "1 + 2 + b";
    t_string "pretty no parens 2" (pretty (Times(Times(Num(1), Num(2)), Num(3))))
      "1 * 2 * 3";
    t_string "example" (pretty (Plus(Plus(Times(Plus(Num(5), Variable("y")), Variable("x")), Num(2)), Num(1))))
      "(5 + y)x + 2 + 1"
];;

let all_arith_tests =
  get_tests @
  contains_tests @
  add_tests @
  evaluate_tests @
  pretty_tests
;;

let arith_suite = "arithmetic_evaluation">:::all_arith_tests
;;

run_test_tt_main arith_suite
;;

let all_sexp_tests = [
    t_any "(1" (parse  "(1")
      (Error "Unmatched left paren at line 0, col 0");

    t_any "(true" (parse "(true")
      (Error "Unmatched left paren at line 0, col 0");

    t_any "(true))" (parse "(true))")
      (Error "Unmatched right paren at line 0, col 6");

    t_any "(a" (parse_toks (tokenize "(a"))
      (Error "Unmatched left paren at line 0, col 0");

    t_any "(a (b c" (parse_toks (tokenize "(a (b c"))
      (Error "Unmatched left paren at line 0, col 3");

    t_any "(" (parse "(")
      (Error "Unmatched left paren at line 0, col 0");

    t_any ")" (parse ")")
      (Error "Unmatched right paren at line 0, col 0");

    t_any "(true a b (1 false)))" (parse  "(true a b (1 false)))")
      (Error "Unmatched right paren at line 0, col 20");

    t_any "(true (a b (1 false)" (parse  "(true (a b (1 false)")
      (Error "Unmatched left paren at line 0, col 6");

    t_any "empty string" (parse "")
      (Ok[]);

    t_any "a" (parse "a")
      (Ok[Sym("a", (0,0,0,1))]);

    t_any "michael" (parse "michael")
      (Ok[Sym("michael", (0,0,0,7))]);

    t_any "1" (parse "1")
      (Ok[Int(1, (0,0,0,1))]);

    t_any "11" (parse "11")
      (Ok[Int(11, (0,0,0,2))]);

    t_any "111" (parse "111")
      (Ok[Int(111, (0,0,0,3))]);

    t_any "true" (parse "true")
      (Ok[Bool(true, (0,0,0,4))]);

    t_any "false" (parse "false")
      (Ok[Bool(false, (0,0,0,5))]);

    t_any "(1)" (parse  "(1)")
      (Ok [Nest ([Int (1, (0, 1, 0, 2))],
                 (0, 0, 0, 3))]);

    t_any "(true)" (parse  "(true)")
      (Ok [Nest ([Bool (true, (0, 1, 0, 5))],
                 (0, 0, 0, 6))]);

    t_any "(a)" (parse  "(a)")
      (Ok [Nest ([Sym ("a", (0, 1, 0, 2))], (0, 0, 0, 3))]);

    t_any "(a b))" (parse  "(a b)")
      (Ok [Nest ([Sym ("a", (0, 1, 0, 2));
                  Sym("b", (0, 3, 0, 4))],
                 (0, 0, 0, 5))]);

    t_any "(1 2 3 4 5 6 7 8 9 10)" (parse  "(1 2 3 4 5 6 7 8 9 10)")
      (Ok [Nest ([Int (1, (0, 1, 0, 2));
                  Int (2, (0, 3, 0, 4));
                  Int (3, (0, 5, 0, 6));
                  Int (4, (0, 7, 0, 8));
                  Int (5, (0, 9, 0, 10));
                  Int (6, (0, 11, 0, 12));
                  Int (7, (0, 13, 0, 14));
                  Int (8, (0, 15, 0, 16));
                  Int (9, (0, 17, 0, 18));
                  Int (10, (0, 19, 0, 21));],
                 (0, 0, 0, 22))]);

    t_any "(a (b true) 3)" (parse_toks (tokenize "(a (b true) 3)"))
      (Ok [Nest
             ([Sym ("a", (0, 1, 0, 2));
               Nest ([Sym ("b", (0, 4, 0, 5));
                      Bool (true, (0, 6, 0, 10))],
                     (0, 3, 0, 11));
               Int (3, (0, 12, 0, 13))],
              (0, 0, 0, 14))]);

    t_any "(1 2 (3 4 5) 6 7 (8 9) 10)" (parse  "(1 2 (3 4 5) 6 7 (8 9) 10)")
      (Ok [Nest ([Int (1, (0, 1, 0, 2));
                  Int (2, (0, 3, 0, 4));
                  Nest([Int (3, (0, 6, 0, 7));
                        Int (4, (0, 8, 0, 9));
                        Int (5, (0, 10, 0, 11));],
                       (0, 5, 0, 12));
                  Int (6, (0, 13, 0, 14));
                  Int (7, (0, 15, 0, 16));
                  Nest([Int (8, (0, 18, 0, 19));
                        Int (9, (0, 20, 0, 21));],
                       (0, 17, 0, 22));
                  Int (10, (0, 23, 0, 25));],
                 (0, 0, 0, 26))]);

    t_any "(a (true) (false) (true) 3)" (parse_toks (tokenize "(a (true) (false) (true) 3)"))
      (Ok [Nest
             ([Sym ("a", (0, 1, 0, 2));
               Nest ([Bool (true, (0, 4, 0, 8))],
                     (0, 3, 0, 9));
               Nest ([Bool (false, (0, 11, 0, 16))],
                     (0, 10, 0, 17));
               Nest ([Bool (true, (0, 19, 0, 23))],
                     (0, 18, 0, 24));
               Int (3, (0, 25, 0, 26))],
              (0, 0, 0, 27))]);

    t_any "(a\n (true)\n (false)\n (true)\n 3)" (parse_toks (tokenize "(a\n (true)\n (false)\n (true)\n 3)"))
      (Ok [Nest
             ([Sym ("a", (0, 1, 0, 2));
               Nest ([Bool (true, (1, 2, 1, 6))],
                     (1, 1, 1, 7));
               Nest ([Bool (false, (2, 2, 2, 7))],
                     (2, 1, 2, 8));
               Nest ([Bool (true, (3, 2, 3, 6))],
                     (3, 1, 3, 7));
               Int (3, (4, 1, 4, 2))],
              (0, 0, 4, 3))]);

    t_any "(a) (b)" (parse  "(a) (b)")
      (Ok [Nest ([Sym ("a", (0, 1, 0, 2));], (0, 0, 0, 3));
           Nest ([Sym ("b", (0, 5, 0, 6));], (0, 4, 0, 7))]);

    t_any "a b" (parse  "a b")
      (Ok [Sym ("a", (0, 0, 0, 1));
           Sym ("b", (0, 2, 0, 3));]);

    t_any "a (a)" (parse "a (a)")
      (Ok [Sym ("a", (0, 0, 0, 1));
           Nest ([Sym ("a", (0, 3, 0, 4))],
                 (0, 2, 0, 5))]);

    t_any "12 (3)" (parse "12 (3)")
      (Ok[Int(12, (0, 0, 0, 2));
          Nest([Int(3, (0, 4, 0, 5))],
               (0, 3, 0, 6))]);

    t_any "true (false)" (parse "true (false)")
      (Ok[Bool(true, (0, 0, 0, 4));
          Nest([Bool(false, (0, 6, 0, 11))],
               (0, 5, 0, 12))]);

    t_any "true\n (\nfalse\n)" (parse "true\n (\nfalse\n)")
      (Ok[Bool(true, (0, 0, 0, 4));
          Nest([Bool(false, (2, 0, 2, 5))],
               (1, 1, 3, 1))]);

    t_any "(true 1) a" (parse "(true 1) a")
      (Ok[Nest ([Bool(true, (0, 1, 0, 5));
                 Int(1, (0, 6, 0, 7))],
                (0, 0, 0, 8));
          Sym("a", (0, 9, 0, 10))]);

    t_any "(true\n1)\na" (parse "(true\n1)\na")
      (Ok[Nest ([Bool(true, (0, 1, 0, 5));
                 Int(1, (1, 0, 1, 1))],
                (0, 0, 1, 2));
          Sym("a", (2, 0, 2, 1))]);

    t_any "true 1 a" (parse_one (tokenize "true 1 a"))
      (Ok(Bool(true, (0, 0, 0, 4)), [(TInt(1, (0,5,0,6))); (TSym ("a", (0,7,0,8)))]));

    (* helper tests when figuring out Sexp2 *)

    (* t_any "1)" (parse_one (tokenize "1)")) *)
      (* (Ok((Int(1, (0, 0, 0, 1))), *)
          (* [(RPAREN (0, 1, 0, 2))])); *)

    (* t_any "1)" (parse_many (tokenize "1)")) *)
      (* (Ok([(Int(1, (0, 0, 0, 1)))], [])); *)

    (* t_any "true 1)" (parse_many (tokenize "true 1)")) *)
      (* (Ok([Bool(true, (0, 0, 0, 4)); *)
                 (* (Int(1, (0,5,0,6)))], *)
          (* [])); *)

    (* t_any "true 1) a" (parse_many (tokenize "true 1) a")) *)
      (* (Ok([Bool(true, (0, 0, 0, 4)); *)
                 (* (Int(1, (0,5,0,6)))], *)
          (* [(TSym ("a", (0,8,0,9)))])); *)

    (* t_any "(true 1) a" (parse_one (tokenize "(true 1) a")) *)
      (* (Ok(Nest([Bool(true, (0, 1, 0, 5)); *)
                (* (Int(1, (0,6,0,7)))], *)
               (* (0,0,0,8)), *)
          (* [(TSym ("a", (0,9,0,10)))])); *)
  ]
;;

let sexp_suite = "sexp_parsing">:::all_sexp_tests
;;

run_test_tt_main sexp_suite
;;
