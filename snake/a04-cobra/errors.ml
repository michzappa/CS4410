open Printf
open Exprs
open Pretty

(* TODO: Define any additional exceptions you want *)
exception ParseError of string (* parse-error message *)

exception NotYetImplemented of string (* TODO: Message to show *)

exception InternalCompilerError of string (* Major failure: message to show *)

exception BindingError of string (* problem with an identifier: message to show *)

exception LanguageLimitationError of string (* compile-time error for language lacking capability*)

(* Stringifies a list of compilation errors *)
let print_errors (exns : exn list) : string list =
  List.map
    (fun e ->
      match e with
      | ParseError msg -> "Parse error: " ^ msg
      | NotYetImplemented msg -> "Not yet implemented: " ^ msg
      | InternalCompilerError msg -> "Internal Compiler Error: " ^ msg
      | BindingError msg -> "Binding error: " ^ msg
      | LanguageLimitationError msg -> "Language limitation: " ^ msg
      | _ -> sprintf "%s" (Printexc.to_string e) )
    exns
;;
