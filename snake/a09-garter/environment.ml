open Exprs
open Utils

type 'a envt = (string * 'a) list

(* The integer represents arity *)
type funenvt = int envt

let native_fun_env : funenvt = [("print", 1); ("input", 0); ("equal", 2)]

let hidden_native_functions : string list =
  ["error"; "assert_tuple_len"; "print_raw"; "try_gc"; "print_stack"]
;;

let free_vars ?(bound : string list = []) (e : 'a aexpr) : string list =
  let rec free_vars_aexpr (e : 'a aexpr) (bound : string list) =
    match e with
    | ALet (name, bind, body, _) ->
        free_vars_cexpr bind bound @ free_vars_aexpr body (name :: bound)
    | ASeq (left, right, _) ->
        free_vars_cexpr left bound @ free_vars_aexpr right bound
    | ACExpr expr -> free_vars_cexpr expr bound
    | ALetRec (bindings, body, _) ->
        let bindings_names = List.map fst bindings in
        let new_scope = bound @ bindings_names in
        let bindings_free_vars =
          flat_map (fun (_, bind) -> free_vars_cexpr bind new_scope) bindings
        in
        bindings_free_vars @ free_vars_aexpr body (bound @ bindings_names)
  and free_vars_cexpr (e : 'a cexpr) (bound : string list) : string list =
    let help (imm : 'a immexpr) = free_vars_immexpr imm bound in
    match e with
    | CIf (_cond, _then, _else, _) ->
        help _cond @ free_vars_aexpr _then bound @ free_vars_aexpr _else bound
    | CPrim1 (_, operand, _) -> help operand
    | CLPrim2 (_, left, right, _) -> help left @ free_vars_aexpr right bound
    | CEPrim2 (_, left, right, _) -> help left @ help right
    | CLambda (_, _, fvs, _) ->
        List.filter (fun name -> not (List.mem name bound)) fvs
    | CNativeApp (_, args, _) -> flat_map help args
    | CApp (func, args, _) -> help func @ flat_map help args
    | CImmExpr expr -> free_vars_immexpr expr bound
    | CTuple (elements, _) -> flat_map help elements
    | CGetItem (tup, index, _) -> help tup @ help index
    | CSetItem (tup, index, value, _) -> help tup @ help index @ help value
  and free_vars_immexpr (e : 'a immexpr) (bound : string list) : string list =
    match e with
    | ImmId (name, _) -> if List.mem name bound then [] else [name]
    | ImmNil _ | ImmNum _ | ImmBool _ -> []
  in
  List.sort_uniq String.compare (free_vars_aexpr e bound)
;;
