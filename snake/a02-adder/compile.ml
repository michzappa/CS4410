open Printf
open Sexp

(* Abstract syntax of (a small subset of) x86 assembly instructions *)

let word_size = 8

type reg =
  | RAX
  | RSP

type arg =
  | Const of int64
  | Reg of reg
  | RegOffset of int * reg (* int is # words of offset *)

type instruction =
  | IMov of arg * arg
  | IAdd of arg * arg
  | IRet

(* A helper function for looking up a name in a "dictionary" and
   returning the associated value if possible.  This is definitely
   not the most efficient data structure for this, but it is nice
   and simple... *)
let rec find (ls : (string * 'a) list) (x : string) : 'a option =
  match ls with
  | [] -> None
  | (y, v) :: rest ->
      if y = x then
        Some v
      else
        find rest x
;;

(* Concrete syntax of the Adder language:

   ‹expr›:
     | NUMBER
     | IDENTIFIER
     | ( let ( ‹bindings› ) ‹expr› )
     | ( add1 ‹expr› )
     | ( sub1 ‹expr› )
   ‹bindings›:
     | ( IDENTIFIER ‹expr› )
     | ( IDENTIFIER ‹expr› ) ‹bindings›
*)

(* Abstract syntax of the Adder language *)

type prim1 =
  | Add1
  | Sub1

type 'a expr =
  | Number of int64 * 'a
  | Id of string * 'a
  | Let of (string * 'a expr) list * 'a expr * 'a
  | Prim1 of prim1 * 'a expr * 'a

(* Function to convert from unknown s-expressions to Adder exprs
   Throws a SyntaxError message if there's a problem
*)
exception SyntaxError of string

let rec expr_of_sexp (s : pos sexp) : pos expr =
  match s with
  | Sym (x, p) -> Id (x, p)
  | Int (n, p) -> Number (n, p)
  | Bool (b, p) ->
      raise
        (SyntaxError
           (sprintf "Non-supported boolean value '%b' at %s" b
              (pos_to_string p false) ) )
  | Nest ([Sym ((("add1" | "sub1") as op), _); exp], p) ->
      let parsed_exp = expr_of_sexp exp in
      let prim =
        if op = "add1" then
          Add1
        else
          Sub1
      in
      Prim1 (prim, parsed_exp, p)
  | Nest (Sym ((("add1" | "sub1") as op), _) :: _, p) ->
      raise
        (SyntaxError
           (sprintf "'%s' expression must have exactly one argument from %s" op
              (pos_to_string p true) ) )
  | Nest ([Sym ("let", _); Nest ([], p); _], _) ->
      raise
        (SyntaxError
           (sprintf "'let' must contain at least one binding from %s"
              (pos_to_string p true) ) )
  | Nest ([Sym ("let", _); Nest (sexp_bindings, _); body], p) ->
      let bindings = bindings_of_sexpr_list sexp_bindings [] in
      Let (bindings, expr_of_sexp body, p)
  | Nest (Sym ("let", _) :: _, p) ->
      raise
        (SyntaxError
           (sprintf "Invalid 'let' expression from %s" (pos_to_string p true))
        )
  | Nest (_, p) ->
      raise
        (SyntaxError
           (sprintf "Invalid expression from %s" (pos_to_string p true)) )

and bindings_of_sexpr_list (sexprs : pos sexp list) (names_seen : string list) :
    (string * pos expr) list =
  match sexprs with
  | [] -> []
  | Nest ([Sym (name, p); _], _) :: _ when List.mem name names_seen ->
      raise
        (SyntaxError
           (sprintf "Name '%s' should not re-occur in 'let' bindings at %s" name
              (pos_to_string p false) ) )
  | Nest ([Sym (name, _); sexp], _) :: rest ->
      (name, expr_of_sexp sexp)
      :: bindings_of_sexpr_list rest (name :: names_seen)
  | Nest (_, p) :: _ ->
      raise
        (SyntaxError
           (sprintf
              "Binding should contain only an identifier and an expression \
               from %s"
              (pos_to_string p true) ) )
  | (Sym (_, p) | Int (_, p) | Bool (_, p)) :: _ ->
      raise
        (SyntaxError
           (sprintf "Bindings should be within parentheses at %s"
              (pos_to_string p false) ) )
;;

(* Functions that implement the compiler *)

(* The next four functions convert assembly instructions into strings,
   one datatype at a time.  Only one function has been fully implemented
   for you. *)
let reg_to_asm_string (r : reg) : string =
  match r with
  | RAX -> "RAX"
  | RSP -> "RSP"
;;

let arg_to_asm_string (a : arg) : string =
  match a with
  | Const n -> sprintf "%Ld" n
  | Reg r -> reg_to_asm_string r
  | RegOffset (offset, reg) ->
      let reg_asm = reg_to_asm_string reg in
      let offset_abs = Int.abs offset in
      let offset_string =
        match offset with
        | 0 -> reg_asm
        | n when n > 0 -> sprintf "%s + %d*%d" reg_asm word_size offset_abs
        | _ -> sprintf "%s - %d*%d" reg_asm word_size offset_abs
      in
      sprintf "[%s]" offset_string
;;

let instruction_to_asm_string (i : instruction) : string =
  match i with
  | IMov (dest, value) ->
      sprintf "\tmov %s, %s" (arg_to_asm_string dest) (arg_to_asm_string value)
  | IAdd (dest, value) ->
      sprintf "\tadd %s, %s" (arg_to_asm_string dest) (arg_to_asm_string value)
  | IRet -> "\tret"
;;

let to_asm_string (is : instruction list) : string =
  List.fold_left
    (fun s i -> sprintf "%s\n%s" s (instruction_to_asm_string i))
    "" is
;;

(* The exception to be thrown when some sort of problem is found with names *)
exception BindingError of string

(* The actual compilation process.  The `compile` function is the primary
   function, and uses `compile_env` as its helper.  In a more idiomatic OCaml
   program, this helper would likely be a local definition within `compile`,
   but separating it out makes it easier for you to test it. *)
let rec compile_env
    (p : pos expr)
      (* the program, currently annotated with source location info *)
    (stack_index : int) (* the next available stack index *)
    (env : (string * int) list) : instruction list =
  (* the current binding environment of names to stack slots *)

  (* the instructions that would execute this program *)
  match p with
  | Number (n, _) -> [IMov (Reg RAX, Const n)]
  | Id (name, p) -> (
    match find env name with
    | Some offset -> [IMov (Reg RAX, RegOffset (offset, RSP))]
    | None ->
        raise
          (BindingError
             (sprintf "Unknown variable '%s' at %s" name (pos_to_string p false))
          ) )
  | Prim1 (op, body, _) ->
      let operand =
        if op = Add1 then
          1L
        else
          -1L
      in
      let compiled_body = compile_env body stack_index env in
      compiled_body @ [IAdd (Reg RAX, Const operand)]
  | Let (bindings, body, _) -> compile_let_env bindings body stack_index env

and compile_let_env
    (bindings : (string * pos expr) list)
    (body : pos expr)
    (stack_index : int)
    (env : (string * int) list) : instruction list =
  match bindings with
  | [] -> compile_env body stack_index env
  | (identifier, bound_expr) :: rest ->
      let compiled_bound_expr = compile_env bound_expr stack_index env in
      let new_env = (identifier, -stack_index) :: env in
      let new_stack_index = stack_index + 1 in
      compiled_bound_expr
      @ [IMov (RegOffset (-stack_index, RSP), Reg RAX)]
      @ compile_let_env rest body new_stack_index new_env
;;

let compile (p : pos expr) : instruction list =
  compile_env p 1
    [] (* Start at the first stack slot, with an empty environment *)
;;

(* The entry point for the compiler: a function that takes a expr and
   creates an assembly-program string representing the compiled version *)
let compile_to_string (prog : pos expr) : string =
  let prelude =
    "\nsection .text\nglobal our_code_starts_here\nour_code_starts_here:"
  in
  let asm_string = to_asm_string (compile prog @ [IRet]) in
  let asm_program = sprintf "%s%s\n" prelude asm_string in
  asm_program
;;
