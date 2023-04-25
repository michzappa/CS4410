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

(* Parses tokens into a list of s expressions, which are either parenthized expressions or atoms. *)
let rec parse_toks (toks : pos tok list) : (pos sexp list, string) result =
  match toks with
  | [] -> Ok[]
  | (LPAREN p) :: rest ->
     (* Report error from earlier tokens first. *)
     (match parse_parenthized_sexp rest [Nest([], p)] with
      | Ok(sexp, rem) ->
         (* Then parse the rest and con. *)
         (match parse_toks rem with
          | Ok(sexps) -> Ok(sexp :: sexps)
          | Error(e) -> Error(e))
      | Error(e) -> Error(e))
  | (RPAREN p) :: rest ->
     Error (sprintf "Unmatched right paren at %s" (pos_to_string p false))
  | atom :: rest ->
     (* parse_atom doesn't create any error worth returning, only
        report those from the rest of the parsing. *)
     (match parse_toks rest with
      | Ok(sexps) -> Ok((parse_atom atom) :: sexps)
      | Error(e) -> Error(e))

(* Parses tokens into a parenthized sexp. *)
and parse_parenthized_sexp (toks : pos tok list) (open_sexps : pos sexp list)
    : (pos sexp * pos tok list, string) result =
  (* - open_sexps is a stack of most recent sexps, this function's
     call sequence starts with one Nest entry representing the overall
     sexp.
     - invariant: open_sexps is never empty
     - invariant: open_sexps only contains Nest's *)
  (* returns (sexp, remaining tokens) or error. *)
  match toks with
  (* If we're still in this function when out of tokens something has
     gone wrong. If a sexp has not been closed, error. *)
  | [] ->
     (match open_sexps with
      | [] -> failwith "invariant failed: no open sexps while in parse_parenthized_sexp"
      | Nest(sexps, p_start) :: tail
        -> Error (sprintf "Unmatched left paren at %s" (pos_to_string p_start false))
      | _ :: _ -> failwith "invariant failed: open_sexps contained a non-Nest")
  (* Push an empty Nest sexp onto open_sexps, this is now the current sexp. *)
  | (LPAREN p) :: rest ->
     parse_parenthized_sexp rest (Nest([], p) :: open_sexps)
  (* Close the current sexp. *)
  | (RPAREN p) :: rest ->
     (match open_sexps with
      | [] -> failwith "invariant failed: no open sexps while in parse_parenthized_sexp"
      (* If there is an outer sexp, put the current sexp inside it. *)
      | Nest(sexps_current, p_start_current) :: (Nest(sexps_outer, p_start_outer) :: tail) ->
         parse_parenthized_sexp rest
           ((Nest(sexps_outer @ [ Nest(sexps_current, pos_range p_start_current p) ],
                  p_start_outer))
            :: tail)
      (* - If the current sexp is the only open sexp, return it (as
         well as the remaining tokens). *)
      | [Nest(sexps, p_start)]
        -> Ok((Nest(sexps, pos_range p_start p)), rest)
      | _ :: _ -> failwith "invariant failed: open_sexps contained a non-Nest")
  (* Add atom to current sexp. *)
  | atom :: rest ->
     (match open_sexps with
      | [] ->
         failwith "invariant failed: no open sexps while in parse_parenthized_sexp"
      | Nest(sexps, p) :: tail ->
         parse_parenthized_sexp rest (Nest(sexps @ [ parse_atom atom ], p) :: tail)
      | _ :: _ -> failwith "invariant failed: open_sexps contained a non-Nest")

(* Parse token into an atomic sexp. *)
and parse_atom (atom: pos tok) : pos sexp =
  (* invariant: this function is only given TSym, TInt, TBool *)
  match atom with
  | (TSym (sym, p)) -> Sym (sym, p)
  | (TInt (num, p)) -> Int (num, p)
  | (TBool (bl, p)) -> Bool (bl, p)
  | _ -> failwith "invariant failed: given token not an atom"
;;

(* Convenience function for tokenizing and parsing. *)
let parse str =
  parse_toks (tokenize str)
;;
