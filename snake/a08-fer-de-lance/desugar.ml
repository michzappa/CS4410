open Printf
open Exprs
open Errors
open Utils
open Environment

let desugar (p : unit program) : unit program =
  let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_%d" name !next
  in
  (* Helper to desugar both defs and lambdas *)
  let rec helpFunc param_binds body =
    (* Lower Tuple and Blank parameters into Let's in the function body *)
    let original_binds_and_desugared_names =
      List.map
        (fun b ->
          match b with
          | BName _ -> (b, None)
          | BTuple _ -> (b, Some (gensym "tuple_param$"))
          | BBlank _ -> (b, Some (gensym "blank_param$")) )
        param_binds
    in
    (* Function parameters, all Names *)
    let new_params =
      List.map
        (fun (original, desugared) ->
          match desugared with
          | None -> original
          | Some name -> BName (name, false, ()) )
        original_binds_and_desugared_names
    in
    (* Additional Let bindings inside function body *)
    let new_binds =
      List.filter_map
        (fun (original, desugared) ->
          Option.map (fun name -> (original, EId (name, ()), ())) desugared )
        original_binds_and_desugared_names
    in
    let new_body = ELet (new_binds, body, ()) in
    ELambda (new_params, helpE new_body, ())
  and helpE (e : unit expr) =
    match e with
    | ENumber (n, _) -> ENumber (n, ())
    | EBool (b, _) -> EBool (b, ())
    | ENil _ -> ENil ()
    | EId (v, _) -> EId (v, ())
    | ETuple (exprs, _) -> ETuple (List.map helpE exprs, ())
    | EGetItem (tup, idx, _) -> EGetItem (helpE tup, helpE idx, ())
    | ESetItem (tup, idx, rhs, _) ->
        ESetItem (helpE tup, helpE idx, helpE rhs, ())
    | EPrim1 (op, expr, _) -> EPrim1 (op, helpE expr, ())
    | EPrim2 (op, lhs, rhs, _) -> EPrim2 (op, helpE lhs, helpE rhs, ())
    | EIf (c, t, f, _) -> EIf (helpE c, helpE t, helpE f, ())
    | EApp (EId (fname, _), args, _) when List.mem_assoc fname native_fun_env ->
        ENativeApp (fname, List.map helpE args, ())
    | EApp (fname, args, _) -> EApp (fname, List.map helpE args, ())
    | ELambda (param_binds, body, _) -> helpFunc param_binds body
    | ESeq (lhs, rhs, _) -> ESeq (helpE lhs, helpE rhs, ())
    | ELet ([], body, _) -> helpE body
    | ELet ((BBlank _, expr, _) :: rest, body, _) ->
        ESeq (helpE expr, helpE (ELet (rest, body, ())), ())
    | ELet ((BTuple (binds, _), value, _) :: rest, body, _) ->
        let tmp_name = gensym "tuple_tmp$" in
        let assert_call =
          let num_binds = binds |> List.length |> Int64.of_int in
          ENativeApp
            ( "assert_tuple_len",
              [EId (tmp_name, ()); ENumber (num_binds, ())],
              () )
        in
        let tmp_binding = (BName (tmp_name, false, ()), helpE value, ()) in
        let new_binds =
          List.mapi
            (fun i b ->
              ( b,
                EGetItem (EId (tmp_name, ()), ENumber (Int64.of_int i, ()), ()),
                () ) )
            binds
        in
        let new_body = helpE (ELet (new_binds, ELet (rest, body, ()), ())) in
        ELet ([tmp_binding], ESeq (assert_call, new_body, ()), ())
    | ELet ((BName (name, shadow, _), value, _) :: rest, body, _) ->
        ELet
          ( [(BName (name, shadow, ()), helpE value, ())],
            helpE (ELet (rest, body, ())),
            () )
    | ELetRec (bindings, body, _) ->
        let new_bindings =
          List.map
            (fun (bind, expr, _) ->
              match bind with
              | BName _ -> (bind, helpE expr, ())
              | BTuple _ | BBlank _ -> ice "desugar found non-name in ELetRec"
              )
            bindings
        in
        let new_body = helpE body in
        ELetRec (new_bindings, new_body, ())
    | ENativeApp (name, _, _) ->
        ice (sprintf "encountered native call <%s> in desugar" name)
  and helpD (d : unit decl) : string * unit expr =
    match d with
    | DFun (fname, param_binds, body, _) -> (fname, helpFunc param_binds body)
  in
  match p with
  | Program (decls, body, _) ->
      let new_program =
        List.fold_right
          (fun decl_group body ->
            let bindings =
              decl_group |> List.map helpD
              |> List.map (fun (fname, lambda) ->
                     raise_if
                       ( match lambda with
                       | ELambda _ -> false
                       | _ -> true )
                       (InternalCompilerError
                          "desugar decl should return lambda" );
                     (BName (fname, true, ()), lambda, ()) )
            in
            ELetRec (bindings, body, ()) )
          decls (helpE body)
      in
      let native_closure_bindings =
        List.map
          (fun (f, a) ->
            let closure_args = iota a |> List.map (fun _ -> gensym "param$") in
            ( BName (f, true, ()),
              ELambda
                ( List.map (fun a -> BName (a, true, ())) closure_args,
                  ENativeApp
                    (f, List.map (fun a -> EId (a, ())) closure_args, ()),
                  () ),
              () ) )
          native_fun_env
      in
      let new_program = ELet (native_closure_bindings, new_program, ()) in
      Program ([], new_program, ())
;;
