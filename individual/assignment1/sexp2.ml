(* THIS IS NOT WHAT I SUBMITTED, BUT WHAT I DID AFTER TALKING WITH PROF LERNER ABOUT THE MUTUAL RECURSION SOLUTION *)
open Unix
open Str
open Printf

type 'a tok =
  | LPAREN of 'a
  | RPAREN of 'a
  | TSym of string * 'a
  | TInt of int * 'a
  | TBool of bool * 'a

let tok_info t =
  match t with
  | LPAREN x -> x
  | RPAREN x -> x
  | TSym (_, x) -> x
  | TInt (_, x) -> x
  | TBool (_, x) -> x
;;

(* startline, startcol, endline, endcol *)
type pos = int * int * int * int
let pos_to_string (startline, startcol, endline, endcol) range =
  if range then
    Printf.sprintf "line %d, col %d--line %d, col %d" startline startcol endline endcol
  else
    Printf.sprintf "line %d, col %d" startline startcol
;;

let tokenize (str : string) : pos tok list =
  let (toks, _, _) = List.fold_left
    (fun ((toks : pos tok list), (line : int), (col : int)) (tok : Str.split_result) ->
      match tok with
      | Delim t ->
         if t = " " then (toks, line, col + 1)
         else if t = "\t" then (toks, line, col + 1)
         else if t = "\n" then (toks, line + 1, 0)
         else if t = "(" then (LPAREN (line, col, line, col + 1) :: toks, line, col + 1)
         else if t = ")" then (RPAREN (line, col, line, col + 1) :: toks, line, col + 1)
         else
           let tLen = String.length t
           in ((TSym (t, (line, col, line, col + tLen))) :: toks, line, col + tLen)
      | Text t ->
         if t = "true" then (TBool (true, (line, col, line, col + 4)) :: toks, line, col + 4)
         else if t = "false" then (TBool (false, (line, col, line, col + 5)) :: toks, line, col + 5)
         else
           let tLen = String.length t
           in try ((TInt (int_of_string t, (line, col, line, col + tLen))) :: toks, line, col + tLen) with
              | Failure _ -> (TSym (t, (line, col, line, col + tLen)) :: toks, line, col + tLen)
    )
    ([], 0, 0)
    (full_split (regexp "[()\n\t ]") str)
  in List.rev toks
;;

(* tokenize explanation *)
(* Given a string tokenize creates a list of tokens, as defined by the
   above grammar, annotated with their position in the original
   string. This position is a 'pos' tuple containing the start/end for
   the token. The current position of the tokenizer is stored in the
   accumulator tuple passed through the List.fold_left, being adjusted
   appropriately for each token produced.

   fold_left is tail-recursive and thus performs better on very
   lengthy lists. But more importantly (and actually related to the
   tail-recursive-ness) fold_left applies the given reduction function
   to the arguments of the given list IN THE SAME ORDER AS THE LIST.
   This is critical for the tokenizer since the line/col state needs
   to be correct with/respect to the order of the tokens.

   The only values in this language are symbols, ints, and bools.
   Bools are a small group so they can be explictly checked, but
   there are way too many ints to check each option. Thus the try/with
   attempts to parse the text as an int, but if it fails it just
   throws it into a symbol.

   The tokens are "scanned" from the given string by splitting
   everything between whitespace or parens. However, these lexical
   items are kept around for the later tokenizing - either for making
   an actual token (parens) or informing the position accumulator
   (whitespace). *)

type 'a sexp =
  | Sym of string * 'a
  | Int of int * 'a
  | Bool of bool * 'a
  | Nest of 'a sexp list * 'a

let sexp_info s =
  match s with
  | Sym (_, x) -> x
  | Int (_, x) -> x
  | Bool (_, x) -> x
  | Nest (_, x) -> x
;;

(* Helper to create a new pos which is the range from the first given
   to the second. *)
let pos_range (pos1 : pos) (pos2 : pos) : pos =
  match pos1 with
  | (startline1, startcol1, endline1, endcol1) ->
     match pos2 with
     | (startline2, startcol2, endline2, endcol2) ->
        (startline1, startcol1, endline2, endcol2)
;;

type s_expression = Nil | Atom of string | Pair of s_expression * s_expression

let rec parse tokens =
    match tokens with
    | [] -> failwith "Syntax error: end of input"
    | "(" :: rest ->
        (match parselist rest with
        | (sexpr, ")" :: rest') ->  (sexpr, rest')
        | _ -> failwith "Syntax error: unmatched ("
        )
    | ")" :: _ -> failwith "Syntax error: unmatched )"
    | atom :: rest -> (Atom atom, rest)


and parselist tokens =
    match tokens with
    | [] | ")" :: _ -> (Nil, tokens)
    | _ ->
        let (sexpr1, rest) = parse tokens in
        let (sexpr2, rest') = parselist rest in
        (Pair (sexpr1, sexpr2), rest')

(* Parses tokens into a list of s expressions, which are either parenthized expressions or atoms. *)
let rec parse_toks (toks : pos tok list) : (pos sexp list, string) result =
  match parse_many toks with
  | Ok(sexps, []) -> Ok(sexps)
  | Ok(_, t :: rest) -> Error(sprintf "Incomplete expression starting at %s"
                                (pos_to_string (tok_info t) false))
  | Error(e) -> Error(e)

and parse_many (toks : pos tok list) : (pos sexp list * pos tok list, string) result =
  match toks with
  | [] -> Ok([], [])
  | (RPAREN p) :: rest -> Ok([], toks)
  | _ ->
     (match parse_one toks with
      | Ok(sexp, rest) ->
         (match parse_many rest with
          | Ok(sexps, rest) -> Ok(sexp :: sexps, rest)
          | Error(e) -> Error(e))
      | Error(e) -> Error(e))

and parse_one (toks : pos tok list) : (pos sexp * pos tok list, string) result =
  match toks with
  | [] -> Error("End of input")
  | (TSym (sym, p)) :: rest -> Ok(Sym (sym, p), rest)
  | (TInt (num, p)) :: rest -> Ok(Int (num, p), rest)
  | (TBool (bl, p)) :: rest -> Ok(Bool (bl, p), rest)
  | (LPAREN p) :: rest ->
     (match parse_many rest with
      | Ok(sexps, (RPAREN p_end) :: rest) ->
         Ok(Nest(sexps, pos_range p p_end), rest)
      | Ok(_) -> Error (sprintf "Unmatched left paren at %s" (pos_to_string p false))
      | Error(e) -> Error(e))
  | (RPAREN p) :: rest -> Error (sprintf "Unmatched right paren at %s" (pos_to_string p false))
;;

(* Convenience function for tokenizing and parsing. *)
let parse str =
  parse_toks (tokenize str)
;;
