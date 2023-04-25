open Printf
open Exprs
open Errors
open Utils
open Environment

(* EString with interpolation -> concatenated string
   - An interpolated variable is delimited by '{' and '}'.
   - '{{' is the escape sequence for a single '{'
   - '}}' is the escape sequence for a single '}'
   - Leading and trailing whitespace is allowed inside '{}'
   Error Situations:
   - Unclosed '{': "{a"
   - Unexpected '}': "a}"
   - Unexpected '{' (while looking for a closing brace): "{a {b}"
   - Non-identifier string within '{ }': "{a b}"
*)

let interpolate_string (str : string) (loc : sourcespan) : sourcespan expr =
  let rec parse_interp
      (char_list : char list)
      (is_inside_id : bool)
      (current_string : string)
      (strings_and_ids : string list) =
    match char_list with
    | [] when is_inside_id ->
        raise (InterpolationExpectedClosingBrace (str, loc))
    | [] -> current_string :: strings_and_ids
    | '{' :: '{' :: rest when not is_inside_id ->
        parse_interp rest false (current_string ^ "{") strings_and_ids
    | '{' :: _ when is_inside_id ->
        raise (InterpolationUnexpectedOpeningBrace (str, loc))
    | '{' :: rest ->
        parse_interp rest true "" (current_string :: strings_and_ids)
    | '}' :: '}' :: rest when not is_inside_id ->
        parse_interp rest false (current_string ^ "}") strings_and_ids
    | '}' :: _ when not is_inside_id ->
        raise (InterpolationUnexpectedClosingBrace (str, loc))
    | '}' :: rest ->
        let trimmed_id = String.trim current_string in
        (* Validate with the same regexp as defines parsing identifier. *)
        raise_if
          (not
             (Str.string_match
                (Str.regexp "^[a-zA-Z_][a-zA-Z0-9_]*$")
                trimmed_id 0 ) )
          (InterpolationInvalidIdentifier (trimmed_id, loc));
        parse_interp rest false "" (trimmed_id :: strings_and_ids)
    | c :: rest ->
        parse_interp rest is_inside_id
          (current_string ^ Printf.sprintf "%c" c)
          strings_and_ids
  in
  let exploded_str = str |> String.to_seq |> List.of_seq in
  let string_ids = List.rev (parse_interp exploded_str false "" []) in
  let exprs =
    string_ids
    |> List.fold_left
         (fun (acc, is_str) str_or_id ->
           let expr =
             if is_str then
               EString (str_or_id, loc)
             else
               ENativeApp ("to_string", [EId (str_or_id, loc)], loc)
           in
           (expr :: acc, not is_str) )
         ([], true)
    |> fst |> List.rev
  in
  let rec concat_exprs (exprs : sourcespan expr list) : sourcespan expr =
    match exprs with
    | [] -> raise (InternalCompilerError "No exprs encountered in interpolation")
    | expr :: [] -> expr
    | EString ("", _) :: rest -> concat_exprs rest
    | expr :: EString ("", _) :: rest -> concat_exprs (expr :: rest)
    | expr :: rest -> EStrConcat (expr, concat_exprs rest, loc)
  in
  concat_exprs exprs
;;

let desugar_interpolations (p : sourcespan program) : sourcespan program =
  let rec helpE expr =
    match expr with
    | ENumber _ | EBool _ | EId _ | ENil _ -> expr
    | EString (str, loc) -> interpolate_string str loc
    | ETuple (elms, loc) -> ETuple (List.map helpE elms, loc)
    | EStrConcat (sl, sr, loc) -> EStrConcat (helpE sl, helpE sr, loc)
    | EStrSlice (str, low, high, loc) ->
        EStrSlice (helpE str, helpE low, helpE high, loc)
    | EStrSliceNoHigh (str, low, loc) ->
        EStrSliceNoHigh (helpE str, helpE low, loc)
    | EGetItem (tup, idx, loc) -> EGetItem (helpE tup, helpE idx, loc)
    | ESetItem (tup, idx, value, loc) ->
        ESetItem (helpE tup, helpE idx, helpE value, loc)
    | EPrim1 (op, expr, loc) -> EPrim1 (op, helpE expr, loc)
    | EPrim2 (op, lhs, rhs, loc) -> EPrim2 (op, helpE lhs, helpE rhs, loc)
    | ELambda (args, expr, loc) -> ELambda (args, helpE expr, loc)
    | ENativeApp (name, exprs, loc) ->
        ENativeApp (name, List.map helpE exprs, loc)
    | EApp (func, exprs, loc) -> EApp (helpE func, List.map helpE exprs, loc)
    | EIf (cond, thn, els, loc) -> EIf (helpE cond, helpE thn, helpE els, loc)
    | ESeq (lhs, rhs, loc) -> ESeq (helpE lhs, helpE rhs, loc)
    | ELet (binds, body, loc) ->
        ELet
          ( List.map (fun (name, bind, loc) -> (name, helpE bind, loc)) binds,
            helpE body,
            loc )
    | ELetRec (binds, body, loc) ->
        ELetRec
          ( List.map (fun (name, bind, loc) -> (name, helpE bind, loc)) binds,
            helpE body,
            loc )
  in
  let helpD decl =
    match decl with
    | DFun (name, binds, expr, loc) -> DFun (name, binds, helpE expr, loc)
  in
  match p with
  | Program (decls, expr, loc) ->
      Program (List.map (List.map helpD) decls, helpE expr, loc)
;;

let desugar (p : unit program) : unit program =
  let gensym = make_gensym () in
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
          | Some name -> BName (name, ()) )
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
    | EString (s, _) -> EString (s, ())
    | ETuple (exprs, _) -> ETuple (List.map helpE exprs, ())
    | EStrConcat (sl, sr, _) ->
        ENativeApp ("str_concat", List.map helpE [sl; sr], ())
    | EStrSlice (str, low, high, _) ->
        ENativeApp ("str_slice", List.map helpE [str; low; high], ())
    | EStrSliceNoHigh (str, low, _) ->
        ENativeApp
          ( "str_slice",
            List.map helpE [str; low; ENativeApp ("len", [str], ())],
            () )
    | EGetItem (tup, idx, _) -> EGetItem (helpE tup, helpE idx, ())
    | ESetItem (tup, idx, rhs, _) ->
        ESetItem (helpE tup, helpE idx, helpE rhs, ())
    | EPrim1 (op, expr, _) -> EPrim1 (op, helpE expr, ())
    | EPrim2 (op, lhs, rhs, _) -> EPrim2 (op, helpE lhs, helpE rhs, ())
    | EIf (c, t, f, _) -> EIf (helpE c, helpE t, helpE f, ())
    | ENativeApp (fname, args, _) -> ENativeApp (fname, List.map helpE args, ())
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
        let tmp_binding = (BName (tmp_name, ()), helpE value, ()) in
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
    | ELet ((BName (name, _), value, _) :: rest, body, _) ->
        ELet
          ( [(BName (name, ()), helpE value, ())],
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
                     (BName (fname, ()), lambda, ()) )
            in
            ELetRec (bindings, body, ()) )
          decls (helpE body)
      in
      Program ([], new_program, ())
;;

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
let add_native_lambdas (p : unit program) : unit program =
  match p with
  | Program ([], body, ()) ->
      let native_closure_bindings : unit binding list =
        List.map
          (fun (f, a) ->
            let closure_args = List.init a (sprintf "param$%d") in
            ( BName (f, ()),
              ELambda
                ( List.map (fun a -> BName (a, ())) closure_args,
                  ENativeApp
                    (f, List.map (fun a -> EId (a, ())) closure_args, ()),
                  () ),
              () ) )
          native_fun_env
      in
      Program ([], ELet (native_closure_bindings, body, ()), ())
  | Program (_, _, ()) -> ice "program with decls in add_native_lambdas"
;;
