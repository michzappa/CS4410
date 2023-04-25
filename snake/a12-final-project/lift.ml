open Exprs
open Errors
open Utils

let debug_print (e : 'a) = debug_printf "%s\n" (ExtLib.dump e)

let lift_read_only (p : 'a aprogram) : 'a aprogram =
  let gensym = make_gensym () in
  let rec helpA (ro_sofar : (read_only_data * string) list) (e : 'a aexpr) :
      (read_only_data * string) list * 'a aexpr =
    debug_print "aexpr";
    debug_print ro_sofar;
    match e with
    | ASeq (lhs, rhs, a) ->
        let ro_sofar, lifted_lhs = helpC ro_sofar lhs in
        let ro_sofar, lifted_rhs = helpA ro_sofar rhs in
        (ro_sofar, ASeq (lifted_lhs, lifted_rhs, a))
    | ALet (name, bind, body, a) ->
        let ro_sofar, lifted_bind = helpC ro_sofar bind in
        let ro_sofar, lifted_body = helpA ro_sofar body in
        (ro_sofar, ALet (name, lifted_bind, lifted_body, a))
    | ALetRec (binds, body, a) ->
        let ro_sofar, lifted_binds =
          List.fold_right
            (fun (name, lambda) (ro_acc, lambda_acc) ->
              let ro_acc, lifted_lambda = helpC ro_acc lambda in
              (ro_acc, (name, lifted_lambda) :: lambda_acc) )
            binds (ro_sofar, [])
        in
        let ro_sofar, lifted_body = helpA ro_sofar body in
        (ro_sofar, ALetRec (lifted_binds, lifted_body, a))
    | ACExpr c ->
        let ro_sofar, lifted = helpC ro_sofar c in
        (ro_sofar, ACExpr lifted)
  and helpC (ro_sofar : (read_only_data * string) list) (c : 'a cexpr) :
      (read_only_data * string) list * 'a cexpr =
    debug_print "cexpr";
    debug_print ro_sofar;
    match c with
    | CPrim1 (op, e, a) ->
        let ro_sofar, lifted = helpI ro_sofar e in
        (ro_sofar, CPrim1 (op, lifted, a))
    | CEPrim2 (op, lhs, rhs, a) ->
        let ro_sofar, lifted_lhs = helpI ro_sofar lhs in
        let ro_sofar, lifted_rhs = helpI ro_sofar rhs in
        (ro_sofar, CEPrim2 (op, lifted_lhs, lifted_rhs, a))
    | CLPrim2 (op, lhs, rhs, a) ->
        let ro_sofar, lifted_lhs = helpI ro_sofar lhs in
        let ro_sofar, lifted_rhs = helpA ro_sofar rhs in
        (ro_sofar, CLPrim2 (op, lifted_lhs, lifted_rhs, a))
    | CIf (cond, thn, els, a) ->
        let ro_sofar, lifted_cond = helpI ro_sofar cond in
        let ro_sofar, lifted_thn = helpA ro_sofar thn in
        let ro_sofar, lifted_els = helpA ro_sofar els in
        (ro_sofar, CIf (lifted_cond, lifted_thn, lifted_els, a))
    | CNativeApp (name, args, a) ->
        let ro_sofar, lifted_args =
          List.fold_right
            (fun arg (ro_acc, args_acc) ->
              let ro_acc, lifted_arg = helpI ro_acc arg in
              (ro_acc, lifted_arg :: args_acc) )
            args (ro_sofar, [])
        in
        (ro_sofar, CNativeApp (name, lifted_args, a))
    | CApp (name, args, a) ->
        let ro_sofar, lifted_name = helpI ro_sofar name in
        let ro_sofar, lifted_args =
          List.fold_right
            (fun arg (ro_acc, args_acc) ->
              let ro_acc, lifted_arg = helpI ro_acc arg in
              (ro_acc, lifted_arg :: args_acc) )
            args (ro_sofar, [])
        in
        (ro_sofar, CApp (lifted_name, lifted_args, a))
    | CImmExpr i ->
        let ro_sofar, lifted = helpI ro_sofar i in
        (ro_sofar, CImmExpr lifted)
    | CTuple (elems, a) ->
        if List.length elems == 0 then
          let mock_ro_data = EmptyTuple in
          match List.assoc_opt mock_ro_data ro_sofar with
          | Some ro_id -> (ro_sofar, CImmExpr (ImmROId (ro_id, ROTuple, a)))
          | None ->
              let ro_id = gensym "rotuple$" in
              ( (mock_ro_data, ro_id) :: ro_sofar,
                CImmExpr (ImmROId (ro_id, ROTuple, a)) )
        else
          let ro_sofar, lifted_elems =
            List.fold_right
              (fun arg (ro_acc, args_acc) ->
                let ro_acc, lifted_arg = helpI ro_acc arg in
                (ro_acc, lifted_arg :: args_acc) )
              elems (ro_sofar, [])
          in
          (ro_sofar, CTuple (lifted_elems, a))
    | CGetItem (tup, ind, a) ->
        let ro_sofar, lifted_tup = helpI ro_sofar tup in
        let ro_sofar, lifted_ind = helpI ro_sofar ind in
        (ro_sofar, CGetItem (lifted_tup, lifted_ind, a))
    | CSetItem (tup, ind, value, a) ->
        let ro_sofar, lifted_tup = helpI ro_sofar tup in
        let ro_sofar, lifted_ind = helpI ro_sofar ind in
        let ro_sofar, lifted_value = helpI ro_sofar value in
        (ro_sofar, CSetItem (lifted_tup, lifted_ind, lifted_value, a))
    | CROLambda _ -> ice "Encountered ICE in lift"
    | CLambda (args, body, [], a) ->
        let ro_id = gensym "rolambda$" in
        let ro_sofar, lifted_body = helpA ro_sofar body in
        ( (EmptyFvLambda (List.length args), ro_id) :: ro_sofar,
          CROLambda (ro_id, args, lifted_body, a) )
    | CLambda (args, body, fvs, a) ->
        let ro_sofar, lifted_body = helpA ro_sofar body in
        (ro_sofar, CLambda (args, lifted_body, fvs, a))
  and helpI (ro_sofar : (read_only_data * string) list) (i : 'a immexpr) :
      (read_only_data * string) list * 'a immexpr =
    debug_print "immexpr";
    debug_print ro_sofar;
    match i with
    | ImmNil _ -> (ro_sofar, i)
    | ImmId _ -> (ro_sofar, i)
    | ImmNum _ -> (ro_sofar, i)
    | ImmBool _ -> (ro_sofar, i)
    | ImmString (s, a) -> (
        debug_print ro_sofar;
        let mock_ro_data = String s in
        match List.assoc_opt mock_ro_data ro_sofar with
        | Some ro_id -> (ro_sofar, ImmROId (ro_id, ROString, a))
        | None ->
            let ro_id = gensym "rostring$" in
            ((mock_ro_data, ro_id) :: ro_sofar, ImmROId (ro_id, ROString, a)) )
    | ImmROId _ -> ice "Found ImmROId in lift"
  in
  match p with
  | AProgram (body, [], a) ->
      let read_onlys, lifted_body = helpA [] body in
      debug_print read_onlys;
      AProgram (lifted_body, read_onlys, a)
  | _ -> ice "AProgram with non-empty read_only list in lift"
;;
