(* Abstract syntax of (a small subset of) x86 assembly instructions *)
open Int64

type sourcespan = Lexing.position * Lexing.position

type tag = int

type prim1 =
  | Add1
  | Sub1
  | Print
  | IsBool
  | IsNum
  | Not
  | PrintStack

type prim2 =
  | Plus
  | Minus
  | Times
  | And
  | Or
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq

type 'a bind = string * 'a expr * 'a

and 'a expr =
  | ENumber of int64 * 'a
  | EBool of bool * 'a
  | EId of string * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ELet of 'a bind list * 'a expr * 'a

and 'a program = 'a expr
