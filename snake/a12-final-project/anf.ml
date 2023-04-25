open Printf
open Exprs
open Errors
open Environment

(* This data type lets us keep track of how a binding was introduced.
   We'll use it to discard unnecessary Seq bindings, and to distinguish
   letrec from let. Essentially, it accumulates just enough information
   in our binding list to tell us how to reconstruct an appropriate aexpr. *)
type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program ([], body, _) -> AProgram (helpA body, [], ())
    | Program (_ :: _, _, _) ->
        ice "Top-level declarations should have been desugared away"
  and helpC (e : tag expr) : unit cexpr * unit anf_bind list =
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
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELet ((BName (bind, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet ((BTuple (_, _), _, _) :: _, _, _) ->
        ice "Tuple bindings should have been desugared away"
    | ESeq (e1, e2, _) ->
        let e1_ans, e1_setup = helpC e1 in
        let e2_ans, e2_setup = helpC e2 in
        (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)
    | ELambda (args, body, _) ->
        let args =
          List.map
            (fun a ->
              match a with
              | BName (a, _) -> a
              | BTuple _ | BBlank _ ->
                  ice "Encountered non-desugared function param binding in ANF."
              )
            args
        in
        let body = helpA body in
        let fvs = free_vars ~bound:args body in
        (CLambda (args, body, fvs, ()), [])
    | ENativeApp (fname, args, _) ->
        let args_imms, args_setups = args |> List.map helpI |> List.split in
        let args_setups = List.flatten args_setups in
        (CNativeApp (fname, args_imms, ()), args_setups)
    | EApp (func, args, _) ->
        let func_imm, func_setup = helpI func in
        let args_imms, args_setups = args |> List.map helpI |> List.split in
        let args_setups = List.flatten args_setups in
        (CApp (func_imm, args_imms, ()), func_setup @ args_setups)
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
    | ELetRec (bindings, body, _) ->
        let anfed_binds =
          List.map
            (fun (bind, lambda, _) ->
              let name =
                match bind with
                | BTuple _ | BBlank _ ->
                    ice "Encountered non-name LetRec binding in ANF"
                | BName (name, _) -> name
              in
              match lambda with
              | ELambda (_, _, _) ->
                  (* Setup from helpc lambda is [] *)
                  let lambda_ans, _ = helpC lambda in
                  (name, lambda_ans)
              | _ -> ice "Encountered non-lambda LetRec value in ANF" )
            bindings
        in
        let body_ans, body_setup = helpC body in
        (body_ans, [BLetRec anfed_binds] @ body_setup)
    | EStrConcat _ -> ice "Unexpected EStrConcat in anf"
    | EStrSlice _ -> ice "Unexpected EStrSlice in anf"
    | EStrSliceNoHigh _ -> ice "Unexpected EStrSliceNoHigh in anf"
    | ENil _ | ENumber _ | EBool _ | EId _ | EString _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : tag expr) : unit immexpr * unit anf_bind list =
    match e with
    | ENumber (n, _) -> (ImmNum (n, ()), [])
    | EBool (b, _) -> (ImmBool (b, ()), [])
    | EId (name, _) -> (ImmId (name, ()), [])
    | ENil _ -> (ImmNil (), [])
    | EString (s, _) -> (ImmString (s, ()), [])
    | EStrConcat _ -> ice "Unexpected EStrConcat in anf"
    | EStrSlice _ -> ice "Unexpected EStrSlice in anf"
    | EStrSliceNoHigh _ -> ice "Unexpected EStrSliceNoHigh in anf"
    | ESeq (e1, e2, _) ->
        (* Make sure to use helpI to preserve side effects *)
        let _, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (e2_imm, e1_setup @ e2_setup)
    | ETuple (exprs, tag) ->
        let tmp = sprintf "tuple_%d" tag in
        let new_imms, new_setup = List.split (List.map helpI exprs) in
        let new_setup = List.concat new_setup in
        let ans = CTuple (new_imms, ()) in
        (ImmId (tmp, ()), new_setup @ [BLet (tmp, ans)])
    | EGetItem (tup, idx, tag) ->
        let tmp = sprintf "tuple_get_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let ans = CGetItem (tup_imm, idx_imm, ()) in
        (ImmId (tmp, ()), tup_setup @ idx_setup @ [BLet (tmp, ans)])
    | ESetItem (tup, idx, rhs, tag) ->
        let tmp = sprintf "tuple_get_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let rhs_imm, rhs_setup = helpI rhs in
        let ans = CSetItem (tup_imm, idx_imm, rhs_imm, ()) in
        (ImmId (tmp, ()), tup_setup @ idx_setup @ rhs_setup @ [BLet (tmp, ans)])
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, ()), arg_setup @ [BLet (tmp, CPrim1 (op, arg_imm, ()))])
    | EPrim2 (EP2 op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( ImmId (tmp, ()),
          left_setup @ right_setup
          @ [BLet (tmp, CEPrim2 (op, left_imm, right_imm, ()))] )
    | EPrim2 (LP2 op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_anf = helpA right in
        ( ImmId (tmp, ()),
          left_setup @ [BLet (tmp, CLPrim2 (op, left_imm, right_anf, ()))] )
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        ( ImmId (tmp, ()),
          cond_setup @ [BLet (tmp, CIf (cond_imm, helpA _then, helpA _else, ()))]
        )
    | ELambda (args, body, tag) ->
        let tmp = sprintf "lambda_%d" tag in
        let args =
          List.map
            (fun a ->
              match a with
              | BName (a, _) -> a
              | BTuple _ | BBlank _ ->
                  ice "Encountered non-desugared function param binding in ANF."
              )
            args
        in
        let body = helpA body in
        let fvs = free_vars ~bound:args body in
        (ImmId (tmp, ()), [BLet (tmp, CLambda (args, body, fvs, ()))])
    | ENativeApp (fname, args, tag) ->
        let tmp = sprintf "native_app_%d" tag in
        let args_imms, args_setups = args |> List.map helpI |> List.split in
        let args_setups = List.flatten args_setups in
        ( ImmId (tmp, ()),
          args_setups @ [BLet (tmp, CNativeApp (fname, args_imms, ()))] )
    | EApp (func, args, tag) ->
        let tmp = sprintf "app_%d" tag in
        let func_imm, func_setup = helpI func in
        let args_imms, args_setups = args |> List.map helpI |> List.split in
        let args_setups = List.flatten args_setups in
        ( ImmId (tmp, ()),
          func_setup @ args_setups @ [BLet (tmp, CApp (func_imm, args_imms, ()))]
        )
    | ELet ([], body, _) -> helpI body
    | ELet ((BName (bind, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet ((_, _, _) :: _, _, _) ->
        ice "Tuple bindings and blanks should have been desugared away"
    | ELetRec (bindings, body, _) ->
        let anfed_binds =
          List.map
            (fun (bind, lambda, _) ->
              let name =
                match bind with
                | BName (name, _) -> name
                | BTuple _ | BBlank _ ->
                    ice "Encountered non-name LetRec binding in ANF"
              in
              match lambda with
              | ELambda (_, _, _) ->
                  (* Setup from helpc lambda is [] *)
                  let lambda_ans, _ = helpC lambda in
                  (name, lambda_ans)
              | _ -> ice "Encountered non-lambda LetRec value in ANF" )
            bindings
        in
        let body_ans, body_setup = helpI body in
        (body_ans, [BLetRec anfed_binds] @ body_setup)
  (* Hint: use BLetRec for each of the binds, and BLet for the final answer *)
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun bind body ->
        (* Here's where the anf_bind datatype becomes most useful:
           BSeq binds get dropped, and turned into ASeq aexprs.
           BLet binds get wrapped back into ALet aexprs.
           BLetRec binds get wrapped back into ALetRec aexprs.
           Syntactically it looks like we're just replacing Bwhatever with Awhatever,
           but that's exactly the information needed to know which aexpr to build. *)
        match bind with
        | BSeq exp -> ASeq (exp, body, ())
        | BLet (name, exp) -> ALet (name, exp, body, ())
        | BLetRec names -> ALetRec (names, body, ()) )
      ans_setup (ACExpr ans)
  in
  helpP p
;;
