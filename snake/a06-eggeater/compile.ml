open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Utils

type 'a envt = (string * 'a) list

let const_true = 0xFFFFFFFFFFFFFFFFL

let const_false = 0x7FFFFFFFFFFFFFFFL

let const_nil = 0x0000000000000001L

let bool_mask = 0x8000000000000000L

let bool_bit = 63L

let bool_tag = 0x0000000000000007L

let bool_tag_mask = 0x0000000000000007L

let tuple_tag = 0x0000000000000001L

let tuple_tag_mask = 0x0000000000000007L

let num_tag = 0x0000000000000000L

let num_tag_mask = 0x0000000000000001L

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let err_ACCESS_NOT_TUPLE = 6L

let err_INDEX_NOT_NUM = 7L

let err_ACCESS_LOW_INDEX = 8L

let err_ACCESS_HIGH_INDEX = 9L

let err_NIL_DEREF = 10L

let err_OUT_OF_MEMORY = 11L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let heap_reg = R15

let snake_heap_reg_save = "snake_heap_reg_save"

let snake_heap_end_ptr = "heap_end_ptr"

let snake_entry_base_pointer = "snake_entry_base_pointer"

(* You may find some of these helpers useful *)
let find ls x =
  match List.assoc_opt x ls with
  | None -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | Some v -> v
;;

let count_vars e =
  let rec helpA e =
    match e with
    | ALet (Named _, bind, body, _) -> 1 + max (helpC bind) (helpA body)
    (* Blank ALet's binding does not get put on the stack *)
    | ALet (Blank, bind, body, _) -> max (helpC bind) (helpA body)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (_, t, f, _) -> max (helpA t) (helpA f)
    | CLPrim2 (_, _, rhs, _) -> helpA rhs
    | _ -> 0
  in
  helpA e
;;

type funenvt = (call_type * int) envt

let initial_fun_env : funenvt =
  [ (* call_types indicate whether a given function is implemented by something
       in the runtime, as a snake function, as a primop (in case that's useful),
       or just unknown so far *)
    ("print", (Native, 1));
    ("input", (Native, 0));
    ("equal", (Native, 2));
    ("assertTupleLen", (Native, 2)) ]
;;

let rename_and_tag (p : tag program) : tag program =
  let rec rename (env : string envt) p =
    match p with
    | Program (decls, body, tag) ->
        let addToEnv funenv decl =
          match decl with
          | DFun (name, args, _, _) ->
              (name, (Snake, List.length args)) :: funenv
        in
        let funenv = List.fold_left addToEnv initial_fun_env decls in
        Program (List.map (helpD funenv env) decls, helpE funenv env body, tag)
  and helpD funenv env decl =
    match decl with
    | DFun (name, args, body, tag) ->
        let newArgs, env' = helpBS env args in
        DFun (name, newArgs, helpE funenv env' body, tag)
  and helpB env b =
    match b with
    | BBlank _ -> (b, env)
    | BName (name, allow_shadow, tag) ->
        let name' = sprintf "%s_%d" name tag in
        (BName (name', allow_shadow, tag), (name, name') :: env)
    | BTuple (binds, tag) ->
        let binds', env' = helpBS env binds in
        (BTuple (binds', tag), env')
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> ([], env)
    | b :: bs ->
        let b', env' = helpB env b in
        let bs', env'' = helpBS env' bs in
        (b' :: bs', env'')
  and helpBG funenv env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE funenv env e in
        let bindings', env'' = helpBG funenv env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE funenv env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE funenv env e1, helpE funenv env e2, tag)
    | ETuple (es, tag) -> ETuple (List.map (helpE funenv env) es, tag)
    | EGetItem (e, idx, tag) ->
        EGetItem (helpE funenv env e, helpE funenv env idx, tag)
    | ESetItem (e, idx, newval, tag) ->
        ESetItem
          ( helpE funenv env e,
            helpE funenv env idx,
            helpE funenv env newval,
            tag )
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE funenv env arg, tag)
    | EPrim2 (op, left, right, tag) ->
        EPrim2 (op, helpE funenv env left, helpE funenv env right, tag)
    | EIf (c, t, f, tag) ->
        EIf (helpE funenv env c, helpE funenv env t, helpE funenv env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId (name, tag) -> ( try EId (find env name, tag) with Not_found -> e )
    | EApp (name, args, Unknown, tag) ->
        let call_type = fst (find funenv name) in
        EApp (name, List.map (helpE funenv env) args, call_type, tag)
    | EApp (_, _, _, _) ->
        raise
          (InternalCompilerError "Rename found EApp with preassigned call type")
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG funenv env binds in
        let body' = helpE funenv env' body in
        ELet (binds', body', tag)
  in
  rename [] p
;;

(* Returns the stack-index (in words) of the deepest stack index used for any
   of the variables in this expression *)
let deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet (Named name, bind, body, _) ->
        List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ALet (Blank, bind, body, _) ->
        List.fold_left max 0 [helpC bind; helpA body]
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1 (_, i, _) -> helpI i
    | CEPrim2 (_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CLPrim2 (_, i1, i2, _) -> max (helpI i1) (helpA i2)
    | CApp (_, args, _, _) -> List.fold_left max 0 (List.map helpI args)
    | CTuple (elms, _) -> List.fold_left max 0 (List.map helpI elms)
    | CGetItem (tup, idx, _) -> max (helpI tup) (helpI idx)
    | CSetItem (tup, idx, newval, _) ->
        List.fold_left max 0 [helpI tup; helpI idx; helpI newval]
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmNil _ -> 0
    | ImmId (name, _) -> name_to_offset name
  and name_to_offset name =
    match find env name with
    | RegOffset (bytes, RBP) ->
        bytes / (-1 * word_size) (* negative because stack direction *)
    | _ -> 0
  in
  max (helpA e)
    0 (* if only parameters are used, helpA might return a negative value *)
;;

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program (decls, body, _) -> AProgram (List.map helpD decls, helpA body, ())
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun (name, args, body, _) ->
        let args =
          List.map
            (fun a ->
              match a with
              | BName (a, _, _) -> a
              | _ ->
                  raise
                    (InternalCompilerError
                       "Encountered non-desugared function param binding in \
                        ANF." ) )
            args
        in
        ADFun (name, args, helpA body, ())
  and helpC (e : tag expr) : unit cexpr * (abind * unit cexpr) list =
    match e with
    | EPrim1 (op, arg, _) ->
        let arg_imm, arg_setup = helpI arg in
        (CPrim1 (op, arg_imm, ()), arg_setup)
    | EPrim2 (EP2 op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (CEPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EPrim2 (LP2 op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_anf = helpA right in
        (CLPrim2 (op, left_imm, right_anf, ()), left_setup)
    | EIf (cond, _then, _else, _) ->
        let cond_imm, cond_setup = helpI cond in
        (CIf (cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        let anf_binding =
          match bind with
          | BBlank _ -> Blank
          | BName (name, _, _) -> Named name
          | BTuple _ ->
              raise (InternalCompilerError "Encountered Tuple Binding in ANF")
        in
        (body_ans, exp_setup @ [(anf_binding, exp_ans)] @ body_setup)
    | EApp (funname, args, ct, _) ->
        let new_args, new_setup = List.split (List.map helpI args) in
        (CApp (funname, new_args, ct, ()), List.concat new_setup)
    | ESeq (_, _, _) ->
        raise (InternalCompilerError "Encountered Sequence in ANF")
    | ETuple (exprs, _) ->
        let new_imms, new_setup = List.split (List.map helpI exprs) in
        let new_setup = List.concat new_setup in
        let ans = CTuple (new_imms, ()) in
        (ans, new_setup)
    | EGetItem (tup, idx, _) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let ans = CGetItem (tup_imm, idx_imm, ()) in
        (ans, tup_setup @ idx_setup)
    | ESetItem (tup, idx, rhs, _) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let rhs_imm, rhs_setup = helpI rhs in
        let ans = CSetItem (tup_imm, idx_imm, rhs_imm, ()) in
        (ans, tup_setup @ idx_setup @ rhs_setup)
    | ENil _ | ENumber _ | EBool _ | EId _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : tag expr) : unit immexpr * (abind * unit cexpr) list =
    match e with
    | ENumber (n, _) -> (ImmNum (n, ()), [])
    | EBool (b, _) -> (ImmBool (b, ()), [])
    | EId (name, _) -> (ImmId (name, ()), [])
    | ENil _ -> (ImmNil (), [])
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, ()), arg_setup @ [(Named tmp, CPrim1 (op, arg_imm, ()))])
    | EPrim2 (EP2 op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( ImmId (tmp, ()),
          left_setup @ right_setup
          @ [(Named tmp, CEPrim2 (op, left_imm, right_imm, ()))] )
    | EPrim2 (LP2 op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_anf = helpA right in
        ( ImmId (tmp, ()),
          left_setup @ [(Named tmp, CLPrim2 (op, left_imm, right_anf, ()))] )
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        ( ImmId (tmp, ()),
          cond_setup
          @ [(Named tmp, CIf (cond_imm, helpA _then, helpA _else, ()))] )
    | EApp (funname, args, ct, tag) ->
        let tmp = sprintf "app_%d" tag in
        let new_args, new_setup = List.split (List.map helpI args) in
        let new_setup = List.concat new_setup in
        ( ImmId (tmp, ()),
          new_setup @ [(Named tmp, CApp (funname, new_args, ct, ()))] )
    | ELet ([], body, _) -> helpI body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        let anf_binding =
          match bind with
          | BBlank _ -> Blank
          | BName (name, _, _) -> Named name
          | BTuple _ ->
              raise (InternalCompilerError "Encountered Tuple Binding in ANF")
        in
        (body_ans, exp_setup @ [(anf_binding, exp_ans)] @ body_setup)
    | ESeq (_, _, _) ->
        raise (InternalCompilerError "Encountered Sequence in ANF")
    | ETuple (exprs, tag) ->
        let tmp = sprintf "tuple_%d" tag in
        let new_imms, new_setup = List.split (List.map helpI exprs) in
        let new_setup = List.concat new_setup in
        let ans = CTuple (new_imms, ()) in
        (ImmId (tmp, ()), new_setup @ [(Named tmp, ans)])
    | EGetItem (tup, idx, tag) ->
        let tmp = sprintf "tuple_get_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let ans = CGetItem (tup_imm, idx_imm, ()) in
        (ImmId (tmp, ()), tup_setup @ idx_setup @ [(Named tmp, ans)])
    | ESetItem (tup, idx, rhs, tag) ->
        let tmp = sprintf "tuple_get_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let rhs_imm, rhs_setup = helpI rhs in
        let ans = CSetItem (tup_imm, idx_imm, rhs_imm, ()) in
        (ImmId (tmp, ()), tup_setup @ idx_setup @ rhs_setup @ [(Named tmp, ans)])
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun (bind, exp) body -> ALet (bind, exp, body, ()))
      ans_setup (ACExpr ans)
  in
  helpP p
;;

(*
Assignment requirements:
  - A function application with the wrong number of arguments should signal an
    Arity error
  - A function application of a non-existent function should signal an UnboundFun
    error
  - An identifier without a corresponding binding location should report an
    UnboundId error
  - A let binding with duplicate names should report a DuplicateId error
  - A function declaration with duplicate names in the argument list should report
    a DuplicateId error
  - If there are multiple function definitions with the same name, report a
    DuplicateFun error
  - If a numeric constant is too large, report an Overflow error

Design choices which may change in future assignments:
  - Variable names can shadow function names which will prevent the function from
  being used anymore. This effectively unbinds the function.
  - Function names cannot be used as in EId and variable names cannot be used in EApp
    function name. These are treated as TypeUsageError.
  - If a declaration shadows a native function, then we throw a ShadowBuiltin error
*)
let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  (* Module for local types only used within `is_well_formed` *)
  let module L = struct
    (* This local type is temporary until we have runtime representations of
       higher order functions. *)
    type name_type =
      | Variable
      | Function of int
  end in
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
  (* Recursive method to process an expression tree *)
  let rec wfE
      (name_list : (string * (L.name_type * sourcespan)) list)
      (e : sourcespan expr) : exn list =
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
    (* Ids may not exist or they may refer to a function *)
    | EId (name, loc) -> (
      match List.assoc_opt name name_list with
      (* Id not found at all *)
      | None -> [UnboundId (name, loc)]
      (* A function was found, not a variable *)
      | Some (L.Function _, _) -> [TypeUsageError (name, "snakeval", loc)]
      (* Variable was found, all is well *)
      | Some (L.Variable, _) -> [] )
    (* Recur down the body expression *)
    | EPrim1 (_, body, _) -> wfEsub body
    (* Recur down the left and right *)
    | EPrim2 (_, lhs, rhs, _) -> wfEsub lhs @ wfEsub rhs
    (* Recur down the condition, then branch, and else branch *)
    | EIf (c, t, f, _) -> wfEsub c @ wfEsub t @ wfEsub f
    (* Check the name exists and the arity is correct *)
    | EApp (name, args, _, loc) ->
        (* Count the number of expressions provided as arguments *)
        let given_arg_len = List.length args in
        (* Look up the name *)
        let name_errs =
          match List.assoc_opt name name_list with
          (* Function not found at all *)
          | None -> [UnboundFun (name, loc)]
          (* A variable was found, not a function *)
          | Some (L.Variable, _) -> [TypeUsageError (name, "function", loc)]
          (* Function found but the arity does not match *)
          | Some (L.Function expected_arg_len, _)
            when expected_arg_len != given_arg_len ->
              [Arity (expected_arg_len, given_arg_len, loc)]
          (* The function found and the arity matched so all good *)
          | Some (L.Function _, _) -> []
        in
        let args_errs = args |> List.map wfEsub |> List.flatten in
        name_errs @ args_errs
    (* Sanity check that the parser never produces zero length bind lists *)
    | ELet ([], _, _) ->
        raise
          (InternalCompilerError "ELet with zero bindings in `is_well_formed`")
    (* Handle duplicate names, binding errors, and body errors *)
    | ELet (bindings, body, _) ->
        (* Process the duplicate name errors *)
        let bind_names_infos =
          bindings |> List.map bind_of_binding
          |> List.map names_infos_of_bind
          |> List.flatten
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
                |> List.map (fun (name, info) -> (name, (L.Variable, info))) )
                @ names,
                errs @ wfE names expr ) )
            (name_list, []) bindings
        in
        (* Process the body recursively with the new names *)
        let body_errors = wfE new_name_list body in
        dup_names_errors @ binding_errors @ body_errors
    | ESeq (l, r, _) -> wfEsub l @ wfEsub r
    | ETuple (exprs, _) -> exprs |> List.map wfEsub |> List.flatten
    | EGetItem (t, i, _) -> wfEsub t @ wfEsub i
    | ESetItem (t, i, r, _) -> wfEsub t @ wfEsub i @ wfEsub r
    (* Method to process an individual declaration *)
  in
  let wfD
      (name_list : (string * (L.name_type * sourcespan)) list)
      (d : sourcespan decl) : exn list =
    match d with
    (* Currently just one case for global declarations *)
    | DFun (_, arguments, body, _) ->
        let arg_names_infos =
          arguments |> List.map names_infos_of_bind |> List.flatten
        in
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
          List.map
            (fun (name, info) -> (name, (L.Variable, info)))
            arg_names_infos
        in
        (* Process body with arguments at the front of the environment *)
        let func_body_errors = wfE (arg_name_list @ name_list) body in
        (* Concatenate all the errors found *)
        dup_names_errors @ func_body_errors
  in
  match p with
  | Program (decls, body, _) -> (
      let shadow_native_errors =
        decls
        |> List.map (fun (DFun (name, _, _, info)) -> (name, info))
        |> List.filter (fun (n, _) -> List.mem_assoc n initial_fun_env)
        |> List.map (fun (name, info) -> ShadowBuiltin (name, info))
      in
      (* Process any duplicate names in function declarations *)
      let dup_names_errors =
        decls
        (* Extract all function names into a list *)
        |> List.map name_of_decl
        (* Make an error for each duplicated declaration *)
        |> process_duplicate_names
             (fun dupname ->
               decls
               |> List.filter (decl_name_matches dupname)
               |> List.map info_of_decl )
             duplicate_fun
      in
      (* Pull out all function names and arities for the environment *)
      let decl_fn_name_list =
        List.map
          (fun (DFun (name, args, _, info)) ->
            (name, (L.Function (List.length args), info)) )
          decls
      in
      let builtin_fn_name_list =
        initial_fun_env
        |> List.map (fun (name, (_, arity)) ->
               (name, (L.Function arity, (Lexing.dummy_pos, Lexing.dummy_pos))) )
      in
      let fn_name_list = decl_fn_name_list @ builtin_fn_name_list in
      (* Process the errors in each declaration and concatenate *)
      let decl_errors = decls |> List.map (wfD fn_name_list) |> List.concat in
      (* Process the errors in the body expression *)
      let body_errors = wfE fn_name_list body in
      let all_errors =
        shadow_native_errors @ dup_names_errors @ decl_errors @ body_errors
      in
      match all_errors with
      (* If no errors then the code is well formed *)
      | [] -> Ok p
      (* If any errors exist then return all *)
      | errors -> Error errors )
;;

let desugar (p : unit program) : unit program =
  let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_%d" name !next
  in
  let rec helpE (e : unit expr) =
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
    | EApp (fname, args, ct, _) -> EApp (fname, List.map helpE args, ct, ())
    | ESeq (lhs, rhs, _) -> ELet ([(BBlank (), helpE lhs, ())], helpE rhs, ())
    | ELet ([], body, _) -> helpE body
    | ELet ((BTuple (binds, _), value, _) :: rest, body, _) ->
        let tmp_name = gensym "tuple_tmp$" in
        let length_assert_binding =
          let num_binds = binds |> List.length |> Int64.of_int in
          let assert_call =
            EApp
              ( "assertTupleLen",
                [EId (tmp_name, ()); ENumber (num_binds, ())],
                Unknown,
                () )
          in
          (BBlank (), assert_call, ())
        in
        let tmp_binding = (BName (tmp_name, false, ()), value, ()) in
        let new_binds =
          List.mapi
            (fun i b ->
              ( b,
                EGetItem (EId (tmp_name, ()), ENumber (Int64.of_int i, ()), ()),
                () ) )
            binds
        in
        let new_body = helpE (ELet (new_binds, ELet (rest, body, ()), ())) in
        ELet ([tmp_binding; length_assert_binding], new_body, ())
    | ELet (bind :: rest, body, _) ->
        ELet ([bind], helpE (ELet (rest, body, ())), ())
  and helpD (d : unit decl) =
    match d with
    | DFun (fname, param_binds, body, _) ->
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
              Option.map (fun name -> (original, EId (name, ()), ())) desugared
              )
            original_binds_and_desugared_names
        in
        let new_body = ELet (new_binds, body, ()) in
        DFun (fname, new_params, helpE new_body, ())
  in
  match p with
  | Program (decls, body, _) -> Program (List.map helpD decls, helpE body, ())
;;

let naive_stack_allocation (prog : tag aprogram) : tag aprogram * arg envt =
  let rec allocate_decl (decl : tag adecl) : arg envt =
    match decl with
    | ADFun (_, args, body, _) ->
        let args_env =
          List.mapi
            (fun index arg -> (arg, RegOffset (8 * (2 + index), RBP)))
            args
        in
        args_env @ allocate_aexpr body 1
  and allocate_aexpr (expr : tag aexpr) (si : int) : arg envt =
    match expr with
    | ALet (Named name, bind, body, _) ->
        let binding_env =
          (name, RegOffset (8 * ~-si, RBP)) :: allocate_cexpr bind (si + 1)
        in
        binding_env @ allocate_aexpr body (si + 1)
    | ALet (Blank, bind, body, _) ->
        let binding_env = allocate_cexpr bind si in
        binding_env @ allocate_aexpr body si
    | ACExpr expr -> allocate_cexpr expr si
  and allocate_cexpr (expr : tag cexpr) (si : int) : arg envt =
    match expr with
    | CIf (_, _then, _else, _) ->
        allocate_aexpr _then si @ allocate_aexpr _else si
    | CLPrim2 (_, _, rhs, _) -> allocate_aexpr rhs si
    (* These all have immediate arguments, which have already been
       allocated if necessary. *)
    | CPrim1 (_, _, _)
     |CEPrim2 (_, _, _, _)
     |CApp (_, _, _, _)
     |CImmExpr _
     |CTuple (_, _)
     |CGetItem (_, _, _)
     |CSetItem (_, _, _, _) -> []
  in
  let allocate_env (prog : tag aprogram) : arg envt =
    match prog with
    | AProgram (decls, expr, _) ->
        let decls_env = List.flatten (List.map allocate_decl decls) in
        let expr_env = allocate_aexpr expr 1 in
        decls_env @ expr_env
  in
  (prog, allocate_env prog)
;;

let collect_arg_cycles (caller_args : string list) (app_exprs : 'a immexpr list)
    : (int * (string * 'a)) list list =
  (* Collect list of ImmIds in App that refer to caller arguments *)
  let app_exprs_ids_to_args : (int * (string * 'a)) list =
    app_exprs
    (* Add the index of each expression in the App *)
    |> enumerate
    (* Filter to only include arguments referring to caller args *)
    |> List.filter_map (fun (idx, imm) ->
           match imm with
           | ImmNum _ | ImmBool _ | ImmNil _ -> None
           | ImmId (name, a) ->
               if List.mem name caller_args then
                 Some (idx, (name, a))
               else
                 None )
  in
  (* Add indices to the list of caller arguments *)
  let caller_args : (int * string) list = enumerate caller_args in
  (* Fold over the list collect the cycles *)
  let rec collect_cycles (e : (int * (string * 'a)) list) :
      (int * (string * 'a)) list list =
    match e with
    (* Base case that there are no more arguments with cycles *)
    | [] -> []
    (* Pop the first id off, collect all others in the cycle, then process
       remaining ImmId's in the filtered rest *)
    | ((idx, (name, _)) as f) :: rest ->
        (* Fold over the rest, collecting immediates in the cycle, while removing
           them from the rest *)
        let rec find_cycle
            (cur_idx : int)
            (cur_name : string)
            (remaining : (int * (string * 'a)) list) :
            (int * (string * 'a)) list * (int * (string * 'a)) list =
          (* Find the index of the current id in the caller args *)
          let cur_caller_idx : int =
            caller_args |> List.find (fun (_, n) -> cur_name = n) |> fst
          in
          (* The next name in the cycle can come from two locations,
             as we need to consider both this argument clobbering
             something else and something else clobbering this
             argument. *)
          let next_idx_name_a_opt : (int * (string * 'a)) option =
            (* The ImmId in the App's arguments at cur_name's location
               in the caller's arguments *)
            match List.assoc_opt cur_caller_idx remaining with
            (* The index isn't in the remaining but the caller arg might be used
               later *)
            | None -> (
              (* The ImmId in caller_args at cur_name's location in
                 the App's arguments *)
              match List.assoc_opt cur_idx caller_args with
              (* The position does not exist so ignore (technically might be
                 unreachable since we don't support greater arity) *)
              | None -> None
              (* If this ImmId is used in the App, it's part of the cycle *)
              | Some next_name ->
                  List.find_opt (fun (_, (n, _)) -> next_name = n) remaining )
            (* That's all *)
            | Some (next_name, next_a) ->
                Some (cur_caller_idx, (next_name, next_a))
          in
          (* Handle the next in the cycle *)
          match next_idx_name_a_opt with
          (* There is no next so just return the remaining arguments *)
          | None -> ([], remaining)
          (* If there is a next... *)
          | Some (next_idx, (next_name, a)) ->
              (* Delete the next from the remaining *)
              let new_remaining = List.remove_assoc next_idx remaining in
              (* Find the rest of the cycle in the remaining starting from next *)
              let cycle, new_remaining =
                find_cycle next_idx next_name new_remaining
              in
              (* Add next name to this cycle and return remaining *)
              ((next_idx, (next_name, a)) :: cycle, new_remaining)
        in
        (* Find the elements of the cycle and the remaining arguments *)
        let cycle, new_rest = find_cycle idx name rest in
        (* Add the current ImmId to current cycle, then process remaining
           cycles *)
        (f :: cycle) :: collect_cycles new_rest
  in
  (* Collect cycles over all the ImmId's that match caller arg names *)
  collect_cycles app_exprs_ids_to_args
;;

let rec compile_aexpr
    (e : tag aexpr)
    (env : arg envt)
    (caller_args : string list)
    (is_tail : bool) : instruction list =
  match e with
  | ALet (bind, aexp, body, tag) ->
      let let_name, move_inst =
        match bind with
        | Blank -> (sprintf "let$blank#%d" tag, [])
        | Named name ->
            (sprintf "let$%s#%d" name tag, [IMov (find env name, Reg RAX)])
      in
      let bound_value = compile_cexpr aexp env caller_args false in
      let body = compile_aexpr body env caller_args is_tail in
      [ ILineComment (sprintf "Let %s begin:" let_name);
        ILineComment (sprintf "%s: computing bound value" let_name) ]
      @ bound_value
      @ [ILineComment (sprintf "%s: move bound value onto stack" let_name)]
      @ move_inst
      @ [ILineComment (sprintf "%s: executing let body" let_name)]
      @ body
      @ [ILineComment (sprintf "Let %s end:" let_name)]
  | ACExpr e -> compile_cexpr e env caller_args is_tail

and compile_cexpr
    (e : tag cexpr)
    (env : arg envt)
    (caller_args : string list)
    (is_tail : bool) =
  let bool_check_reg reg err_name =
    let err_label = sprintf "error_%s_not_boolean" err_name in
    [ ILineComment (sprintf "Checking %s for boolean-ness" (r_to_asm reg));
      IMov (Reg R11, Reg reg);
      (* Get relevant bits of boolean type tag *)
      IAnd (Reg R11, HexConst bool_tag_mask);
      (* Check whether they match the boolean type tag *)
      ICmp (Reg R11, HexConst bool_tag);
      (* Re-load from source reg after clobbering R11 *)
      IMov (Reg R11, Reg reg);
      (* If argument isn't a tuple, error *)
      IJne err_label;
      ILineComment (sprintf "Done checking %s for boolean-ness" (r_to_asm reg))
    ]
  in
  let non_nil_tuple_check_reg reg =
    let err_label = "error_access_not_tuple" in
    let nil_label = "error_nil_deref" in
    [ ILineComment (sprintf "Checking %s for tuple-ness" (r_to_asm reg));
      IMov (Reg R11, Reg reg);
      (* Get relevant bits of tuple type tag *)
      IAnd (Reg R11, HexConst tuple_tag_mask);
      (* Check whether they match the tuple type tag *)
      ICmp (Reg R11, HexConst tuple_tag);
      (* Re-load from source reg after clobbering R11 *)
      IMov (Reg R11, Reg reg);
      (* If argument isn't a tuple, error *)
      IJne err_label;
      (* Check if the argument is the nil constant *)
      ICmp (Reg R11, HexConst const_nil);
      (* If argument is nil, error *)
      IJe nil_label;
      ILineComment (sprintf "Done checking %s for tuple-ness" (r_to_asm reg)) ]
  in
  let num_check_reg reg err_name =
    let err_label = sprintf "error_%s_not_number" err_name in
    [ ILineComment (sprintf "Checking %s for number-ness" (r_to_asm reg));
      IMov (Reg R11, Reg reg);
      (* Bitwise AND with the flag mask and observe the result *)
      ITest (Reg R11, HexConst num_tag_mask);
      (* Since num_tag is 0x0, error if result was non-zero *)
      IJnz err_label;
      ILineComment (sprintf "Done checking %s for number-ness" (r_to_asm reg))
    ]
  in
  let idx_low_check_reg =
    let err_label = "error_access_low_index" in
    [ ILineComment (sprintf "Checking %s for index low-ness" (r_to_asm R11));
      (* Compare index against zero *)
      ICmp (Reg R11, Const 0L);
      (* Jump to error if R11 is less than zero *)
      IJl err_label;
      ILineComment
        (sprintf "Done checking %s for index low-ness" (r_to_asm R11)) ]
  in
  let idx_high_check_reg_and_convert =
    let err_label = "error_access_high_index" in
    [ ILineComment (sprintf "Checking %s for index high-ness" (r_to_asm R11));
      ISar (Reg R11, Const 1L);
      (* Compare index against tuple size in [RAX] *)
      ICmp (Reg R11, RegOffset (0, RAX));
      (* Jump to error if R11 is greater than or equal to tuple size *)
      IJge err_label;
      ILineComment
        (sprintf "Done checking %s for index high-ness" (r_to_asm R11)) ]
  in
  match e with
  | CImmExpr e -> [IMov (Reg RAX, compile_imm e env)]
  | CPrim1 (((Add1 | Sub1) as op), n, tag) ->
      let prim1_name = sprintf "prim1$%s#%d" (name_of_op1 op) tag in
      let n_arg = compile_imm n env in
      let op_inst =
        match op with
        | Add1 -> IAdd (Reg RAX, Const 2L)
        | Sub1 -> ISub (Reg RAX, Const 2L)
        | _ -> raise (InternalCompilerError "invalid op in nested match")
      in
      [ ILineComment (sprintf "Prim1 %s begin:" prim1_name);
        (* Move in the argument *)
        IMov (Reg RAX, n_arg) ]
      @ num_check_reg RAX "arith"
      @ [ (* Perform operation *)
          op_inst;
          (* After the operation was performed, check for overflow *)
          IJo "error_overflow";
          ILineComment (sprintf "Prim1 %s end:" prim1_name) ]
  | CPrim1 (((IsBool | IsNum | IsTuple) as op), x, tag) ->
      let prim1_name = sprintf "prim1$%s#%d" (name_of_op1 op) tag in
      let done_label = sprintf "done_%d" tag in
      let x_arg = compile_imm x env in
      let tag_mask, tag =
        match op with
        | IsBool -> (bool_tag_mask, bool_tag)
        | IsNum -> (num_tag_mask, num_tag)
        | IsTuple -> (tuple_tag_mask, tuple_tag)
        | _ -> raise (InternalCompilerError "invalid op in nested match")
      in
      [ ILineComment (sprintf "Prim1 %s begin:" prim1_name);
        (* Move in the argument *)
        IMov (Reg RAX, x_arg);
        (* Get relevant bits of type tag *)
        IAnd (Reg RAX, HexConst tag_mask);
        (* Check whether they match the type tag *)
        ICmp (Reg RAX, HexConst tag);
        (* Pre-load true, expecting success *)
        IMov (Reg RAX, HexConst const_true);
        (* If success, we are done *)
        IJe done_label;
        (* If not success, load false and be done *)
        IMov (Reg RAX, HexConst const_false);
        ILabel done_label;
        ILineComment (sprintf "Prim1 %s end:" prim1_name) ]
  | CPrim1 (Not, b, tag) ->
      let prim1_name = sprintf "prim1$%s#%d" (name_of_op1 Not) tag in
      let n_arg = compile_imm b env in
      [ ILineComment (sprintf "Prim1 %s begin:" prim1_name);
        (* Load the argument *)
        IMov (Reg RAX, n_arg) ]
      (* Value check the argument *)
      @ bool_check_reg RAX "logic"
      (* Flip the bit for bool *)
      @ [ IBtc (Reg RAX, Const bool_bit);
          ILineComment (sprintf "Prim1 %s end:" prim1_name) ]
  | CPrim1 (PrintStack, x, tag) ->
      let prim1_name = sprintf "prim1$%s#%d" (name_of_op1 PrintStack) tag in
      let x_arg = compile_imm x env in
      [ ILineComment (sprintf "Prim1 %s begin:" prim1_name);
        (* Set up arguments *)
        IMov (Reg (List.nth first_six_args_registers 0), x_arg);
        IMov (Reg (List.nth first_six_args_registers 1), Reg RSP);
        IMov (Reg (List.nth first_six_args_registers 2), Reg RBP);
        (* Call method with no cleanup necessary after *)
        ICall "print_stack";
        ILineComment (sprintf "Prim1 %s end:" prim1_name) ]
  | CLPrim2 (((And | Or) as op), lhs, rhs, tag) ->
      let prim2_name = sprintf "prim2$%s#%d" (name_of_lop2 op) tag in
      let done_label = sprintf "done_%d" tag in
      let lhs_arg = compile_imm lhs env in
      let rhs_insts = compile_aexpr rhs env caller_args false in
      let jmp_inst =
        match op with
        (* Jump when LHS is false so that AND results in false *)
        | And -> IJne done_label
        (* Jump when LHS is true so that OR results in true *)
        | Or -> IJe done_label
      in
      [ ILineComment (sprintf "Prim2 %s begin:" prim2_name);
        (* Load the argument *)
        IMov (Reg RAX, lhs_arg) ]
      (* Value check the argument *)
      @ bool_check_reg RAX "logic"
      @ [ (* Check if it is true *)
          ICmp (Reg RAX, HexConst const_true);
          (* Jump according to op so we short circuit over rhs *)
          jmp_inst ]
      (* If not short circuit evaluate rhs *)
      @ rhs_insts
      (* Check that rhs was a bool *)
      @ bool_check_reg RAX "logic"
      (* Label for short circuiting *)
      @ [ILabel done_label; ILineComment (sprintf "Prim2 %s end:" prim2_name)]
  | CEPrim2 (((Plus | Minus | Times) as op), lhs, rhs, tag) ->
      let prim2_name = sprintf "prim2$%s#%d" (name_of_eop2 op) tag in
      let lhs_arg = compile_imm lhs env in
      let rhs_arg = compile_imm rhs env in
      let insts =
        match op with
        | Plus -> [IAdd (Reg RAX, Reg R11)]
        | Minus -> [ISub (Reg RAX, Reg R11)]
        | Times -> [ISar (Reg RAX, Const 1L); IMul (Reg RAX, Reg R11)]
        | _ -> raise (InternalCompilerError "invalid op in nested match")
      in
      (* Load lhs *)
      [ ILineComment (sprintf "Prim2 %s begin:" prim2_name);
        IMov (Reg RAX, lhs_arg) ]
      @ num_check_reg RAX "arith"
      (* Load rhs into R11 for checking *)
      @ [IMov (Reg R11, rhs_arg)]
      @ num_check_reg R11 "arith"
      (* Perform computation on RAX and R11 *)
      @ insts
      @ [ (* After the operation was performed, check for overflow *)
          IJo "error_overflow";
          ILineComment (sprintf "Prim2 %s end:" prim2_name) ]
  | CEPrim2 (Eq, lhs, rhs, tag) ->
      let prim2_name = sprintf "prim2$%s#%d" (name_of_eop2 Eq) tag in
      let done_label = sprintf "done_%d" tag in
      let lhs_arg = compile_imm lhs env in
      let rhs_arg = compile_imm rhs env in
      [ ILineComment (sprintf "Prim2 %s begin:" prim2_name);
        (* Load lhs for comparison *)
        IMov (Reg RAX, lhs_arg);
        (* Load rhs for comparison *)
        IMov (Reg R11, rhs_arg);
        (* Compare lhs to rhs *)
        ICmp (Reg RAX, Reg R11);
        (* Pre-load true *)
        IMov (Reg RAX, HexConst const_true);
        (* If lhs == rhs, we are done *)
        IJe done_label;
        (* If lhs != rhs, load false and be done *)
        IMov (Reg RAX, HexConst const_false);
        ILabel done_label;
        ILineComment (sprintf "Prim2 %s end:" prim2_name) ]
  | CEPrim2 (((Greater | GreaterEq | Less | LessEq) as op), lhs, rhs, tag) ->
      let prim2_name = sprintf "prim2$%s#%d" (name_of_eop2 op) tag in
      let done_label = sprintf "done_%d" tag in
      let lhs_arg = compile_imm lhs env in
      let rhs_arg = compile_imm rhs env in
      let jump_inst =
        match op with
        | Greater -> IJg done_label
        | GreaterEq -> IJge done_label
        | Less -> IJl done_label
        | LessEq -> IJle done_label
        | _ -> raise (InternalCompilerError "invalid op in nested match")
      in
      [ ILineComment (sprintf "Prim2 %s begin:" prim2_name);
        (* Load lhs *)
        IMov (Reg RAX, lhs_arg) ]
      @ num_check_reg RAX "comp"
      (* Load rhs into R11 for checking *)
      @ [IMov (Reg R11, rhs_arg)]
      @ num_check_reg R11 "comp"
      (* Compare RAX and R11 *)
      @ [ ICmp (Reg RAX, Reg R11);
          (* Pre-load true *)
          IMov (Reg RAX, HexConst const_true);
          (* If comparison succeeds, jump to done *)
          jump_inst;
          (* If comparison failed, load false and be done *)
          IMov (Reg RAX, HexConst const_false);
          ILabel done_label;
          ILineComment (sprintf "Prim2 %s end:" prim2_name) ]
  | CIf (cond, thn, els, tag) ->
      let if_name = sprintf "if#%d" tag in
      let else_label = sprintf "else_%d" tag in
      let done_label = sprintf "done_%d" tag in
      let c_arg = compile_imm cond env in
      let thn_comp = compile_aexpr thn env caller_args is_tail in
      let els_comp = compile_aexpr els env caller_args is_tail in
      [ ILineComment (sprintf "If %s begin:" if_name);
        ILineComment (sprintf "%s condition check:" if_name);
        (* Load condition and check boolean-ness *)
        IMov (Reg RAX, c_arg) ]
      @ bool_check_reg RAX "if"
      (* Check if condition is true, if not jump to else *)
      @ [ ICmp (Reg RAX, HexConst const_true);
          IJne else_label;
          ILineComment (sprintf "%s then branch:" if_name) ]
      (* Evaluate then and and jump to done *)
      @ thn_comp
      @ [ IJmp done_label;
          (* Evaluate else branch and be done *)
          ILineComment (sprintf "%s else branch:" if_name);
          ILabel else_label ]
      @ els_comp
      @ [ILabel done_label; ILineComment (sprintf "If %s end:" if_name)]
  | CTuple (immexprs, tag) ->
      let tuple_name = sprintf "tuple#%d" tag in
      let tuple_size = List.length immexprs in
      let tuple_size_bytes =
        (* word_size * (header + tuple size + padding?1:0) *)
        word_size * (1 + tuple_size + Int.rem (tuple_size + 1) 2)
      in
      let allocate_tuple =
        [ ILineComment "Allocating tuple on the heap";
          IMov (Reg RAX, Reg heap_reg);
          IAdd (Reg heap_reg, Const (Int64.of_int tuple_size_bytes));
          ILineComment "Check if this overran the heap";
          ICmp (Reg heap_reg, RelLabelContents snake_heap_end_ptr);
          IJg "error_out_of_memory" ]
      in
      let move_tuple_size =
        (* XXX: Tuple size is currently stored as a "normal" number and
           not a snake number. *)
        [ ILineComment "Setting tuple size";
          IMov (Reg R11, Const (Int64.of_int tuple_size));
          IMov (RegOffset (0, RAX), Reg R11) ]
      in
      let move_tuple_items =
        ILineComment "Moving tuple contents onto heap"
        :: ( immexprs
           |> List.mapi (fun idx expr ->
                  [ IMov (Reg R11, compile_imm expr env);
                    IMov (RegOffset (word_size * (idx + 1), RAX), Reg R11) ] )
           |> List.flatten )
      in
      let tag_tuple_pointer =
        [ILineComment "Tagging tuple pointer"; IOr (Reg RAX, HexConst tuple_tag)]
      in
      [ILineComment (sprintf "Tuple %s begin" tuple_name)]
      @ allocate_tuple @ move_tuple_size @ move_tuple_items @ tag_tuple_pointer
      @ [ILineComment (sprintf "Tuple %s end" tuple_name)]
  | CGetItem (tup, idx, tag) ->
      let get_item_name = sprintf "get_tuple#%d" tag in
      let tuple_tag_check =
        IMov (Reg RAX, compile_imm tup env) :: non_nil_tuple_check_reg RAX
      in
      let tuple_untag =
        [IAnd (Reg RAX, HexConst (Int64.lognot tuple_tag_mask))]
      in
      let move_access_index = [IMov (Reg R11, compile_imm idx env)] in
      let check_index_num = num_check_reg R11 "index" in
      let check_index_low = idx_low_check_reg in
      let check_index_high = idx_high_check_reg_and_convert in
      let access_element =
        [IMov (Reg RAX, RegOffsetReg (RAX, R11, word_size, word_size))]
      in
      [ILineComment (sprintf "GetItem %s begin" get_item_name)]
      @ tuple_tag_check @ tuple_untag @ move_access_index @ check_index_num
      @ check_index_low @ check_index_high @ access_element
      @ [ILineComment (sprintf "GetItem %s end" get_item_name)]
  | CSetItem (tup, idx, rhs, tag) ->
      let set_item_name = sprintf "set_tuple#%d" tag in
      let tuple_tag_check =
        IMov (Reg RAX, compile_imm tup env) :: non_nil_tuple_check_reg RAX
      in
      let tuple_untag =
        [IAnd (Reg RAX, HexConst (Int64.lognot tuple_tag_mask))]
      in
      let move_access_index = [IMov (Reg R11, compile_imm idx env)] in
      let check_index_num = num_check_reg R11 "index" in
      let check_index_low = idx_low_check_reg in
      let check_index_high = idx_high_check_reg_and_convert in
      let set_element_and_return_val =
        [ ILea (Reg R11, RegOffsetReg (RAX, R11, word_size, word_size));
          IMov (Reg RAX, compile_imm rhs env);
          IMov (RegOffset (0, R11), Reg RAX) ]
      in
      [ILineComment (sprintf "SetItem %s begin" set_item_name)]
      @ tuple_tag_check @ tuple_untag @ move_access_index @ check_index_num
      @ check_index_low @ check_index_high @ set_element_and_return_val
      @ [ILineComment (sprintf "SetItem %s end" set_item_name)]
  | CApp (name, app_exprs, Snake, tag)
  (* Tail-recursive application for a function defined in snake, all
     arguments go on stack *)
    when is_tail && List.length app_exprs <= List.length caller_args ->
      let app_name = sprintf "app%s#%d" name tag in
      let arg_cycles = collect_arg_cycles caller_args app_exprs in
      let enumerated_app_exprs = enumerate app_exprs in
      (* Instructions to get all the arguments with cycles in order
         for the tail-call, and which arguments can be handled
         "normally" *)
      let compile_cycles
          (cycles : (int * (string * tag)) list list)
          (app_exprs : (int * tag immexpr) list) :
          instruction list * (int * tag immexpr) list =
        List.fold_left
          (fun (sofar, remaining_exprs) cycle ->
            match cycle with
            | [] -> raise (InternalCompilerError "encountered empty cycle")
            (* As the cycle has length 1, no special consideration is
               needed. Ignoring it here, and it will be handled in
               moving_non_cycle_args. *)
            | [_] -> (sofar, remaining_exprs)
            | (index, (name, tag)) :: rest ->
                (* The cycle needs to be broken using a scratch register *)
                let store_cycle_break =
                  [IMov (Reg RAX, compile_imm (ImmId (name, tag)) env)]
                in
                (* But the rest of the cycle can be compiled "normally" *)
                let remaining_cycle =
                  rest
                  |> List.map (fun (idx, (name, tag)) ->
                         [ IMov (Reg R11, compile_imm (ImmId (name, tag)) env);
                           IMov (RegOffset (8 * (2 + idx), RBP), Reg R11) ] )
                  |> List.flatten
                in
                (* The value in the scratch register is then placed on
                   the stack after everything else has been *)
                let restore_cycle_break =
                  [IMov (RegOffset (8 * (2 + index), RBP), Reg RAX)]
                in
                (* Remove these handled arguments from future consideration *)
                let remaining_exprs =
                  List.filter
                    (fun (idx, _) ->
                      not (idx = index || List.mem_assoc idx rest) )
                    remaining_exprs
                in
                ( store_cycle_break @ remaining_cycle @ restore_cycle_break
                  @ sofar,
                  remaining_exprs ) )
          ([], app_exprs) cycles
      in
      let cycle_insts, non_cycle_args =
        compile_cycles arg_cycles enumerated_app_exprs
      in
      let moving_non_cycle_args =
        non_cycle_args
        |> List.map (fun (idx, arg) ->
               [ IMov (Reg R11, compile_imm arg env);
                 IMov (RegOffset (8 * (2 + idx), RBP), Reg R11) ] )
        |> List.flatten
      in
      [ILineComment (sprintf "Tail App %s begin:" app_name)]
      (* Arguments for the tail-call *)
      @ cycle_insts
      @ moving_non_cycle_args
      @ [ (* Reclaim the stack space used for local variables since it
             is set up again after the tail_entry *)
          IMov (Reg RSP, Reg RBP);
          IJmp (sprintf "%s$tail_entry" name);
          ILineComment (sprintf "Tail App %s end:" app_name) ]
  | CApp (name, args, Snake, tag) ->
      (* Non-tail-recursive application for a function defined in
         snake, all arguments go on stack *)
      let app_name = sprintf "app%s#%d" name tag in
      let app_args_len = List.length args in
      let padding_inst, padding_amount =
        if Int.rem app_args_len 2 = 0 then
          (ILineComment "no padding needed before call", 0)
        else
          (IPush (Const 0L), 1)
      in
      let push_args_onto_stack =
        args
        |> List.rev_map (fun a ->
               [IMov (Reg R11, compile_imm a env); IPush (Reg R11)] )
        |> List.flatten
      in
      [ILineComment (sprintf "App %s begin:" app_name); padding_inst]
      @ push_args_onto_stack
      @ [ ICall name;
          (* Reclaim the stack space used for local variables *)
          ISub
            (Reg RSP, Const (Int64.of_int (8 * (app_args_len + padding_amount))));
          ILineComment (sprintf "App %s end:" app_name) ]
  | CApp (fname, args, Native, tag) ->
      (* Application of a function defined in the C runtime, arguments
         follow C calling convention *)
      let app_name = sprintf "Native %s#%d" fname tag in
      let args_in_reg, args_on_stack = split_at 6 args in
      let args_in_reg_inst =
        List.mapi
          (fun idx arg ->
            IMov
              (Reg (List.nth first_six_args_registers idx), compile_imm arg env)
            )
          args_in_reg
      in
      let stack_args_len = List.length args in
      let padding_inst, padding_amount =
        if Int.rem stack_args_len 2 = 0 then
          (ILineComment "no padding needed before call", 0)
        else
          (IPush (Const 0L), 1)
      in
      let push_args_onto_stack =
        args_on_stack
        |> List.rev_map (fun a ->
               [IMov (Reg R11, compile_imm a env); IPush (Reg R11)] )
        |> List.flatten
      in
      let stack_arg_cleanup =
        if stack_args_len > 0 then
          ISub
            ( Reg RSP,
              Const (Int64.of_int (8 * (stack_args_len + padding_amount))) )
        else
          ILineComment "No arguments on the stack"
      in
      [ILineComment (sprintf "App %s begin:" app_name)]
      (* Set up argument in registers *)
      @ args_in_reg_inst
      (* Place stack padding if necessary *)
      @ [padding_inst]
      (* Set up arguments on the stack *)
      @ push_args_onto_stack
      @ [ (* Call method with cleanup afterwards *)
          ICall fname;
          (* Cleanup stack if necessary *)
          stack_arg_cleanup;
          ILineComment (sprintf "App %s end:" app_name) ]
  | CApp (fname, _, Unknown, _) ->
      raise
        (InternalCompilerError
           (sprintf "Encountered Unknown function in compile: %s" fname) )

and compile_imm e env =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> HexConst const_true
  | ImmBool (false, _) -> HexConst const_false
  | ImmId (x, _) -> find env x
  | ImmNil _ -> HexConst const_nil
;;

let compile_fun
    (name : string)
    (args : string list)
    (expr : tag aexpr)
    (env : arg envt) : instruction list * instruction list * instruction list =
  let prelude = [ILabel name] in
  let stack_setup =
    let num_vars = deepest_stack expr env in
    (* If even we increment num_vars to next even number (since we already
       one spot for RBP). This ensures when a function call must be made
       that it uses an even number of stack space to maintain alignment. *)
    let aligned_vars = num_vars + Int.rem num_vars 2 in
    raise_if
      (Int.rem aligned_vars 2 != 0)
      (InternalCompilerError "aligned vars should always be even");
    [ IPush (Reg RBP);
      IMov (Reg RBP, Reg RSP);
      (* Specific entry point for tail-call optimization *)
      ILabel (sprintf "%s$tail_entry" name);
      (* Allocate space for local variables *)
      ISub (Reg RSP, Const (Int64.of_int (8 * aligned_vars))) ]
  in
  let stack_teardown = [IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet] in
  let body = compile_aexpr expr env args true in
  (prelude @ stack_setup, body, stack_teardown)
;;

let compile_decl (d : tag adecl) (env : arg envt) : instruction list =
  match d with
  | ADFun (name, args, expr, _) ->
      let setup, body, teardown = compile_fun name args expr env in
      setup @ body @ teardown
;;

let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  match anfed with
  | AProgram (decls, expr, _) ->
      (* Declare code section, runtime function names, and runtime global
         variables. Must match C code names. *)
      let prelude =
        [ISection ".text"; ILineComment "run-time C functions"]
        @ List.map (fun (n, _) -> IExtern n) initial_fun_env
        @ [ IExtern "error";
            IExtern "print_stack";
            IExtern snake_entry_base_pointer;
            IExtern snake_heap_reg_save;
            IExtern snake_heap_end_ptr ]
      in
      (* Error routines that call non-returning error C function *)
      let error_routines =
        let error_routine (name : string) (code : int64) (reg : reg) =
          [ ILineComment "never returning sub-routine";
            ILabel (sprintf "error_%s" name);
            IMov (Reg RDI, HexConst code);
            IMov (Reg RSI, Reg reg);
            ICall "error";
            ILineComment "should never return" ]
        in
        (* Errors from testing arguments in the scratch register *)
        error_routine "logic_not_boolean" err_LOGIC_NOT_BOOL R11
        @ error_routine "if_not_boolean" err_IF_NOT_BOOL R11
        @ error_routine "arith_not_number" err_ARITH_NOT_NUM R11
        @ error_routine "comp_not_number" err_COMP_NOT_NUM R11
        @ error_routine "access_not_tuple" err_ACCESS_NOT_TUPLE R11
        @ error_routine "nil_deref" err_NIL_DEREF R11
        @ error_routine "index_not_number" err_INDEX_NOT_NUM R11
        (* Overflow errors come from the "answer in RAX" *)
        @ error_routine "overflow" err_OVERFLOW RAX
        @ error_routine "access_low_index" err_ACCESS_LOW_INDEX RAX
        @ error_routine "access_high_index" err_ACCESS_HIGH_INDEX RAX
        (* Register does not matter in this error case *)
        @ error_routine "out_of_memory" err_OUT_OF_MEMORY RAX
      in
      let decls_code =
        decls |> List.map (fun d -> compile_decl d env) |> List.flatten
      in
      let expr_code =
        let setup, body, teardown =
          compile_fun "our_code_starts_here" [] expr env
        in
        let new_setup =
          match setup with
          | [ (ILabel "our_code_starts_here" as i_label);
              (IPush (Reg RBP) as i_save_rbp);
              (IMov (Reg RBP, Reg RSP) as i_rsp_into_rbp);
              (* Ignore the tail_entry label for our_code_starts_here *)
              _;
              (ISub (Reg RSP, Const _) as i_reserve_locals) ] ->
              [ IGlobal "our_code_starts_here";
                i_label;
                i_save_rbp;
                i_rsp_into_rbp;
                i_reserve_locals;
                IMov (RelLabelContents snake_entry_base_pointer, Reg RBP);
                IMov (RelLabelContents snake_heap_reg_save, Reg R15);
                IMov (Reg heap_reg, Reg (List.nth first_six_args_registers 0));
                IAdd (Reg heap_reg, HexConst 15L);
                IAnd (Reg heap_reg, HexConst (Int64.lognot 0x0FL)) ]
          | _ ->
              raise
                (InternalCompilerError
                   "Compilation of our_code_starts_here did not produce global \
                    then label at the front" )
        in
        let new_teardown =
          IMov (Reg R15, RelLabelContents snake_heap_reg_save) :: teardown
        in
        new_setup @ body @ new_teardown
      in
      let full_inst_list = prelude @ decls_code @ expr_code @ error_routines in
      to_asm full_inst_list
;;

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

(* Add a desugaring phase somewhere in here *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  |> add_phase untagged untagP
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings naive_stack_allocation
  |> add_phase result compile_prog
;;
