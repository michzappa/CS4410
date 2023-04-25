open Exprs
open Utils
open Graph

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

let annotate_with_free_vars (prog : tag aprogram) : (tag * freevarst) aprogram =
  let rec helpA (aexp : tag aexpr) : (tag * StringSet.t) aexpr =
    match aexp with
    | ALet (name, bind, body, t) ->
        let annotated_bind = helpC bind in
        let _, fvs_bind = get_tag_C annotated_bind in
        let annotated_body = helpA body in
        let _, fvs_body = get_tag_A annotated_body in
        let freevars =
          StringSet.union fvs_bind (StringSet.remove name fvs_body)
        in
        ALet (name, annotated_bind, annotated_body, (t, freevars))
    | ASeq (left, right, t) ->
        let annotated_left = helpC left in
        let _, fvs_left = get_tag_C annotated_left in
        let annotated_right = helpA right in
        let _, fvs_right = get_tag_A annotated_right in
        let freevars = StringSet.union fvs_left fvs_right in
        ASeq (annotated_left, annotated_right, (t, freevars))
    | ACExpr expr -> ACExpr (helpC expr)
    | ALetRec (bindings, body, t) ->
        let annotated_bindings =
          List.map (fun (name, bind) -> (name, helpC bind)) bindings
        in
        let names, annotated_binds = List.split annotated_bindings in
        let fvs_bindings =
          List.fold_right
            (fun binding acc -> StringSet.union acc (snd (get_tag_C binding)))
            annotated_binds StringSet.empty
        in
        let annotated_body = helpA body in
        let _, fvs_body = get_tag_A annotated_body in
        let freevars =
          StringSet.diff
            (StringSet.union fvs_bindings fvs_body)
            (StringSet.of_list names)
        in
        ALetRec (annotated_bindings, annotated_body, (t, freevars))
  and helpC (cexp : tag cexpr) : (tag * StringSet.t) cexpr =
    match cexp with
    | CPrim1 (op, e, t) ->
        let annotated_e = helpI e in
        let _, fvs_e = get_tag_I annotated_e in
        CPrim1 (op, annotated_e, (t, fvs_e))
    | CEPrim2 (op, e1, e2, t) ->
        let annotated_e1 = helpI e1 in
        let annotated_e2 = helpI e2 in
        let _, fvs_e1 = get_tag_I annotated_e1 in
        let _, fvs_e2 = get_tag_I annotated_e2 in
        CEPrim2
          (op, annotated_e1, annotated_e2, (t, StringSet.union fvs_e1 fvs_e2))
    | CLPrim2 (op, e1, e2, t) ->
        let annotated_e1 = helpI e1 in
        let annotated_e2 = helpA e2 in
        let _, fvs_e1 = get_tag_I annotated_e1 in
        let _, fvs_e2 = get_tag_A annotated_e2 in
        CLPrim2
          (op, annotated_e1, annotated_e2, (t, StringSet.union fvs_e1 fvs_e2))
    | CIf (cond, thn, els, t) ->
        let annotated_cond = helpI cond in
        let annotated_thn = helpA thn in
        let annotated_els = helpA els in
        let _, fvs_cond = get_tag_I annotated_cond in
        let _, fvs_thn = get_tag_A annotated_thn in
        let _, fvs_els = get_tag_A annotated_els in
        CIf
          ( annotated_cond,
            annotated_thn,
            annotated_els,
            (t, StringSet.union fvs_cond (StringSet.union fvs_thn fvs_els)) )
    | CNativeApp (fname, args, t) ->
        let annotated_args = List.map helpI args in
        let fvs_args =
          List.fold_right
            (fun iexpr acc -> StringSet.union (snd (get_tag_I iexpr)) acc)
            annotated_args StringSet.empty
        in
        CNativeApp (fname, annotated_args, (t, fvs_args))
    | CApp (func, args, t) ->
        let annotated_func = helpI func in
        let _, fvs_func = get_tag_I annotated_func in
        let annotated_args = List.map helpI args in
        let fvs_args =
          List.fold_right
            (fun iexpr acc -> StringSet.union (snd (get_tag_I iexpr)) acc)
            annotated_args StringSet.empty
        in
        let freevars = StringSet.union fvs_func fvs_args in
        CApp (annotated_func, annotated_args, (t, freevars))
    | CImmExpr i -> CImmExpr (helpI i)
    | CTuple (els, t) ->
        let annotated_els = List.map helpI els in
        let fvs_els =
          List.fold_right
            (fun iexpr acc -> StringSet.union (snd (get_tag_I iexpr)) acc)
            annotated_els StringSet.empty
        in
        CTuple (annotated_els, (t, fvs_els))
    | CGetItem (e, idx, t) ->
        let annotated_e = helpI e in
        let annotated_idx = helpI idx in
        let _, fvs_e = get_tag_I annotated_e in
        let _, fvs_idx = get_tag_I annotated_idx in
        CGetItem (annotated_e, annotated_idx, (t, StringSet.union fvs_e fvs_idx))
    | CSetItem (e, idx, newval, t) ->
        let annotated_e = helpI e in
        let annotated_idx = helpI idx in
        let annotated_newval = helpI newval in
        let _, fvs_e = get_tag_I annotated_e in
        let _, fvs_idx = get_tag_I annotated_idx in
        let _, fvs_newval = get_tag_I annotated_newval in
        CSetItem
          ( annotated_e,
            annotated_idx,
            annotated_newval,
            (t, StringSet.union fvs_e (StringSet.union fvs_idx fvs_newval)) )
    | CLambda (args, body, free_vars, t) ->
        let annotated_body = helpA body in
        CLambda
          (args, annotated_body, free_vars, (t, StringSet.of_list free_vars))
  and helpI (iexp : tag immexpr) : (tag * StringSet.t) immexpr =
    match iexp with
    | ImmNil t -> ImmNil (t, StringSet.empty)
    | ImmId (n, t) -> ImmId (n, (t, StringSet.singleton n))
    | ImmNum (n, t) -> ImmNum (n, (t, StringSet.empty))
    | ImmBool (b, t) -> ImmBool (b, (t, StringSet.empty))
  in
  match prog with
  | AProgram (body, t) -> AProgram (helpA body, (t, StringSet.empty))
;;
