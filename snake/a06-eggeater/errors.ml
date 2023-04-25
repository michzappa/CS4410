open Printf
open Exprs
open Pretty

(* parse-error message *)
exception ParseError of string

(* name, where used *)
exception UnboundId of string * sourcespan

(* name of fun, where used *)
exception UnboundFun of string * sourcespan

(* name, where used, where defined *)
exception ShadowId of string * sourcespan * sourcespan

(* name, where used *)
exception ShadowBuiltin of string * sourcespan

(* name, where first defined, where redefined *)
exception DuplicateId of string * sourcespan * sourcespan

let duplicate_id (name : string) (fst_def : sourcespan) (re_def : sourcespan) :
    exn =
  DuplicateId (name, fst_def, re_def)
;;

(* name, where first defined, where redefined *)
exception DuplicateFun of string * sourcespan * sourcespan

let duplicate_fun (name : string) (fst_def : sourcespan) (re_def : sourcespan) :
    exn =
  DuplicateFun (name, fst_def, re_def)
;;

(* value, where used *)
exception Overflow of int64 * sourcespan

(* correct arity, given arity, where called *)
exception Arity of int * int * sourcespan

(* TODO: Message to show *)
exception NotYetImplemented of string

exception Unsupported of string * sourcespan

(* Major failure: message to show *)
exception InternalCompilerError of string

(* Later assignments if types are added, this may be deprecated or improved *)
(* variable name, expected type name (function|snakeval), where used *)
exception TypeUsageError of string * string * sourcespan

(* Stringifies a list of compilation errors *)
let print_errors (exns : exn list) : string list =
  List.map
    (fun e ->
      match e with
      | ParseError msg -> msg
      | NotYetImplemented msg -> "Not yet implemented: " ^ msg
      | Unsupported (msg, loc) ->
          sprintf "Unsupported: %s at <%s>" msg (string_of_sourcespan loc)
      | InternalCompilerError msg -> "Internal Compiler Error: " ^ msg
      | UnboundId (x, loc) ->
          sprintf "The identifier %s, used at <%s>, is not in scope" x
            (string_of_sourcespan loc)
      | UnboundFun (x, loc) ->
          sprintf "The function name %s, used at <%s>, is not in scope" x
            (string_of_sourcespan loc)
      | ShadowId (x, loc, existing) ->
          sprintf
            "The identifier %s, defined at <%s>, shadows one defined at <%s>" x
            (string_of_sourcespan loc)
            (string_of_sourcespan existing)
      | ShadowBuiltin (name, loc) ->
          sprintf
            "The identifier %s, defined at <%s>, shadows a builtin identifier"
            name (string_of_sourcespan loc)
      | DuplicateId (x, loc, existing) ->
          sprintf "The identifier %s, redefined at <%s>, duplicates one at <%s>"
            x
            (string_of_sourcespan existing)
            (string_of_sourcespan loc)
      | DuplicateFun (x, loc, existing) ->
          sprintf
            "The function name %s, redefined at <%s>, duplicates one at <%s>" x
            (string_of_sourcespan existing)
            (string_of_sourcespan loc)
      | Overflow (num, loc) ->
          sprintf
            "The number literal %Ld, used at <%s>, is not supported in this \
             language"
            num (string_of_sourcespan loc)
      | Arity (expected, actual, loc) ->
          sprintf
            "The function called at <%s> expected an arity of %d, but received \
             %d arguments"
            (string_of_sourcespan loc) expected actual
      | TypeUsageError (name, typename, loc) ->
          sprintf
            "The bound name '%s', used at <%s>, is not the expected type: %s"
            name (string_of_sourcespan loc) typename
      | _ -> sprintf "%s" (Printexc.to_string e) )
    exns
;;
