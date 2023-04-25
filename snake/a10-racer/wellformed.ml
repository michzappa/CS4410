open Printf
open Phases
open Exprs
open Errors
open Utils
open Environment

(* NOTE: Due to garbage collection, function/lambda arity and tuple length
   should not use the highest bit (i.e. number should be less than 2^63).
   We do not (or at least cannot) check this since OCaml integers use only
   63 bits so when taking the length of a list it would always be valid. *)
let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  (* Higher level function to process duplicate names in a list *)
  let process_duplicate_names
      (get_duplicate_locs : string -> sourcespan list)
      (make_error : string -> sourcespan -> sourcespan -> exn)
      (names : string list) : exn list =
    names
    (* Collect the set of duplicate names *)
    |> collect_duplicates
    (* Process each duplicate names one by one *)
    |> List.map (fun dupname ->
           (* Get the locations of all the duplicate names *)
           let ddlocs = get_duplicate_locs dupname in
           (* Sanity check the length *)
           raise_if
             (List.length ddlocs < 2)
             (InternalCompilerError "Duplicate names should be at least two");
           (* The first location is considered the original binding *)
           let origloc = List.hd ddlocs in
           (* The rest are considered 'duplicated' *)
           let duplocs = List.tl ddlocs in
           (* Make an error out of each of the duplicates *)
           List.map (make_error dupname origloc) duplocs )
    |> List.concat
  in
  let rec wfFunc
      (name_list : (string * sourcespan) list)
      (arguments : sourcespan bind list)
      (body : sourcespan expr) : exn list =
    let arg_names_infos = flat_map names_infos_of_bind arguments in
    (* Process any duplicate names in the argument list *)
    let dup_names_errors =
      arg_names_infos
      (* Extract the names *)
      |> List.map fst
      (* Make an error for each duplicate argument *)
      |> process_duplicate_names
           (fun dupname ->
             arg_names_infos
             |> List.filter (fun (name, _) -> name = dupname)
             |> List.map snd )
           duplicate_id
    in
    (* Extract argument list to use while checking the body *)
    let arg_name_list =
      List.map (fun (name, info) -> (name, info)) arg_names_infos
    in
    (* Process body with arguments at the front of the environment *)
    let func_body_errors = wfE (arg_name_list @ name_list) body in
    (* Concatenate all the errors found *)
    dup_names_errors @ func_body_errors
  (* Recursive method to process an expression tree *)
  and wfE (name_list : (string * sourcespan) list) (e : sourcespan expr) :
      exn list =
    let wfEsub = wfE name_list in
    match e with
    (* Booleans are inherently well-formed *)
    | EBool _ -> []
    (* Nil is inherently well-formed *)
    | ENil _ -> []
    (* Some numbers are out of range of snakeval numbers *)
    | ENumber (n, loc)
      when n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L ->
        (* Effectively we have 63 bit integers *)
        [Overflow (n, loc)]
    (* The remaining numbers are good *)
    | ENumber _ -> []
    (* Ids may not exist *)
    | EId (name, loc) -> (
      match List.assoc_opt name name_list with
      (* Id not found at all *)
      | None -> [UnboundId (name, loc)]
      (* Variable was found, all is well *)
      | Some _ -> [] )
    (* Recur down the body expression *)
    | EPrim1 (_, body, _) -> wfEsub body
    (* Recur down the left and right *)
    | EPrim2 (_, lhs, rhs, _) -> wfEsub lhs @ wfEsub rhs
    (* Recur down the condition, then branch, and else branch *)
    | EIf (c, t, f, _) -> wfEsub c @ wfEsub t @ wfEsub f
    (* We can statically check arity of native functions *)
    | EApp (EId (fname, _), args, loc) when List.mem_assoc fname native_fun_env
      ->
        let arity = List.assoc fname native_fun_env in
        let num_args = List.length args in
        let arity_error =
          match arity = num_args with
          | true -> []
          | false -> [Arity (arity, num_args, loc)]
        in
        (* Check argument(s) *)
        let args_errs = flat_map wfEsub args in
        arity_error @ args_errs
    | EApp (func_expr, args, _) ->
        (* Check for errors in the function expression *)
        let func_expr_errs = wfEsub func_expr in
        (* Check argument(s) *)
        let args_errs = flat_map wfEsub args in
        func_expr_errs @ args_errs
    (* Sanity check that the parser never produces zero length bind lists *)
    | ELet ([], _, _) -> ice "ELet with zero bindings in `is_well_formed`"
    (* Handle duplicate names, binding errors, and body errors *)
    | ELet (bindings, body, _) ->
        (* Process the duplicate name errors *)
        let bind_names_infos =
          bindings |> List.map bind_of_binding |> flat_map names_infos_of_bind
        in
        let dup_names_errors =
          bind_names_infos
          (* Extract all the names *)
          |> List.map fst
          (* Make an error for each duplicate binding *)
          |> process_duplicate_names
               (fun dupname ->
                 bind_names_infos
                 |> List.filter (fun (name, _) -> name = dupname)
                 |> List.map snd )
               duplicate_id
        in
        (* Process the expression in each binding, accumulating scope
           as we go along *)
        let new_name_list, binding_errors =
          List.fold_left
            (fun (names, errs) (bind, expr, _) ->
              ( ( bind |> names_infos_of_bind
                |> List.map (fun (name, info) -> (name, info)) )
                @ names,
                errs @ wfE names expr ) )
            (name_list, []) bindings
        in
        (* Process the body recursively with the new names *)
        let body_errors = wfE new_name_list body in
        dup_names_errors @ binding_errors @ body_errors
    | ESeq (l, r, _) -> wfEsub l @ wfEsub r
    | ETuple (exprs, _) -> flat_map wfEsub exprs
    | EGetItem (t, i, _) -> wfEsub t @ wfEsub i
    | ESetItem (t, i, r, _) -> wfEsub t @ wfEsub i @ wfEsub r
    | ELambda (arguments, body, _) -> wfFunc name_list arguments body
    | ELetRec (bindings, body, _) ->
        let bind_names_infos =
          bindings |> List.map bind_of_binding |> flat_map names_infos_of_bind
        in
        let dup_names_errors =
          bind_names_infos
          (* Extract all the names *)
          |> List.map fst
          (* Make an error for each duplicate binding *)
          |> process_duplicate_names
               (fun dupname ->
                 bind_names_infos
                 |> List.filter (fun (name, _) -> name = dupname)
                 |> List.map snd )
               duplicate_id
        in
        let new_name_list =
          List.map
            (fun (name, _, _) ->
              match name with
              | BName (s, _, info) -> (s, info)
              | BTuple _ | BBlank _ ->
                  ice "is_well_formed found a non-name in ELetRec" )
            bindings
          @ name_list
        in
        let bound_value_errors =
          flat_map
            (fun (name, bind, loc) ->
              match bind with
              | ELambda _ -> wfE new_name_list bind
              | _ -> [LetRecNonFunction (name, loc)] )
            bindings
        in
        let body_errors = wfE new_name_list body in
        dup_names_errors @ bound_value_errors @ body_errors
    | ENativeApp (name, _, _) ->
        ice (sprintf "encountered native call <%s> in is_well_formed" name)
    (* Method to process an individual declaration *)
  in
  let wfD (name_list : (string * sourcespan) list) (d : sourcespan decl) :
      exn list =
    match d with
    (* Currently just one case for global declarations *)
    | DFun (_, arguments, body, _) -> wfFunc name_list arguments body
  in
  match p with
  | Program (decls, body, _) -> (
      let shadow_native_errors =
        decls |> List.flatten |> List.map name_info_of_decl
        |> List.filter (fun (n, _) -> List.mem_assoc n native_fun_env)
        |> List.map (fun (name, info) -> ShadowBuiltin (name, info))
      in
      let native_fn_name_list =
        native_fun_env
        |> List.map (fun (name, _) ->
               (name, (Lexing.dummy_pos, Lexing.dummy_pos)) )
      in
      (* Process the errors in each declaration group and concatenate *)
      let fn_name_list, decl_errors =
        List.fold_left
          (fun (env, err_acc) decl_group ->
            (* Process any duplicate names in function declarations *)
            let dup_names_errors =
              decl_group
              (* Extract all function names into a list *)
              |> List.map name_of_decl
              (* Make an error for each duplicated declaration *)
              |> process_duplicate_names
                   (fun dupname ->
                     decl_group
                     |> List.filter (decl_name_matches dupname)
                     |> List.map info_of_decl )
                   duplicate_fun
            in
            (* Extract names in the group *)
            let names_in_group = List.map name_info_of_decl decl_group in
            (* Add names to the environment *)
            let new_env = names_in_group @ env in
            (* Process each declaration in the new environment *)
            let group_errors = flat_map (wfD new_env) decl_group in
            (* Propagate forward the new environment and errors accumulation *)
            (new_env, err_acc @ dup_names_errors @ group_errors) )
          (native_fn_name_list, []) decls
      in
      (* Process the errors in the body expression *)
      let body_errors = wfE fn_name_list body in
      let all_errors = shadow_native_errors @ decl_errors @ body_errors in
      match all_errors with
      (* If no errors then the code is well formed *)
      | [] -> Ok p
      (* If any errors exist then return all *)
      | errors -> Error errors )
;;
