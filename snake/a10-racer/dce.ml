open Exprs
module SS = Set.Make (String)

type 'a dce_info =
  { exp: 'a;
    is_pure: bool;
    free_vars: SS.t }

let make_info exp is_pure free_vars = {exp; is_pure; free_vars}

let collect_letrec_cycles (name_binds : (string * 'a dce_info) list) :
    (string * 'a dce_info) list list =
  (* Initialize work queue based on first element and differ to create cycle *)
  let rec help_collect (name_binds : ((string * 'a dce_info) * SS.t) list) :
      (string * 'a dce_info) list list =
    match name_binds with
    | [] -> []
    | elm :: rest -> create_cycle [elm] [] rest
  (* Create a single cycle and then defers back to help collect *)
  and create_cycle
      (elem_queue : ((string * 'a dce_info) * SS.t) list)
      (current_cycle : (string * 'a dce_info) list)
      (uncollected : ((string * 'a dce_info) * SS.t) list) :
      (string * 'a dce_info) list list =
    match elem_queue with
    (* Work queue is empty so add cycle and recur on rest for other cycles *)
    | [] -> current_cycle :: help_collect uncollected
    (* Pop first element off the work queue *)
    | ((name, info), fvs) :: rest_queue ->
        (* Add the element to the cycle *)
        let current_cycle = (name, info) :: current_cycle in
        (* Collect the free vars that are in the uncollected elements *)
        let elms_in_fvs, elms_not_in_fvs =
          List.partition
            (fun ((other_name, _), _) -> SS.mem other_name fvs)
            uncollected
        in
        (* Add these to the work queue and recur *)
        create_cycle (rest_queue @ elms_in_fvs) current_cycle elms_not_in_fvs
  in
  (* Create the set of all binding names *)
  let names_set = name_binds |> List.map fst |> SS.of_list in
  name_binds
  (* Filter all the free vars to only contain names from the binding set *)
  |> List.map (fun (name, info) ->
         ((name, info), SS.inter info.free_vars names_set) )
  (* Defer to the helper *)
  |> help_collect
;;

let dead_code_elimination (p : 'p aprogram) : unit aprogram =
  let split_infos infos =
    List.fold_right
      (fun i (acc_exp, acc_pure, acc_fv) ->
        (i.exp :: acc_exp, i.is_pure :: acc_pure, i.free_vars :: acc_fv) )
      infos ([], [], [])
  in
  let list_and bs = List.for_all Fun.id bs in
  let union_sets sets = List.fold_right SS.union sets SS.empty in
  let helpI (imm : 'imm immexpr) : unit immexpr dce_info =
    match imm with
    | ImmNil _ -> make_info (ImmNil ()) true SS.empty
    | ImmBool (b, _) -> make_info (ImmBool (b, ())) true SS.empty
    | ImmNum (n, _) -> make_info (ImmNum (n, ())) true SS.empty
    | ImmId (id, _) -> make_info (ImmId (id, ())) true (SS.singleton id)
  in
  let rec helpA (aexp : 'a aexpr) : unit aexpr dce_info =
    match aexp with
    | ACExpr cexp ->
        let {exp; is_pure; free_vars} = helpC cexp in
        make_info (ACExpr exp) is_pure free_vars
    | ASeq (lhs, rhs, _) ->
        let lhs_info = helpC lhs in
        let rhs_info = helpA rhs in
        if lhs_info.is_pure then
          rhs_info
        else
          { exp= ASeq (lhs_info.exp, rhs_info.exp, ());
            is_pure= false;
            free_vars= SS.union lhs_info.free_vars rhs_info.free_vars }
    | ALet (name, bind, body, _) ->
        let body_info = helpA body in
        let is_name_used = SS.mem name body_info.free_vars in
        let bind_info = helpC bind in
        if (not is_name_used) && bind_info.is_pure then
          body_info
        else if not is_name_used then
          { exp= ASeq (bind_info.exp, body_info.exp, ());
            is_pure= false;
            free_vars= SS.union bind_info.free_vars body_info.free_vars }
        else
          { exp= ALet (name, bind_info.exp, body_info.exp, ());
            is_pure= bind_info.is_pure && body_info.is_pure;
            free_vars=
              SS.union bind_info.free_vars (SS.remove name body_info.free_vars)
          }
    | ALetRec (name_binds, body, _) ->
        let body_info = helpA body in
        let opt_name_binds =
          List.map (fun (name, bind) -> (name, helpC bind)) name_binds
        in
        let cleaned_name_binds =
          opt_name_binds
          (* Collect all the binding cycles *)
          |> collect_letrec_cycles
          (* Filter cycles that are not used in the body *)
          |> List.filter_map (fun cycle_binds ->
                 let cycle_used_in_body =
                   List.exists
                     (fun (name, _) -> SS.mem name body_info.free_vars)
                     cycle_binds
                 in
                 if cycle_used_in_body then Some cycle_binds else None )
          (* Flatten the list of lists for final bindings *)
          |> List.flatten
        in
        if List.length cleaned_name_binds = 0 then
          body_info
        else
          let new_name_binds =
            List.map (fun (name, info) -> (name, info.exp)) cleaned_name_binds
          in
          let bind_free_vars =
            List.map (fun (_, info) -> info.free_vars) cleaned_name_binds
          in
          let free_vars =
            SS.diff
              (union_sets (body_info.free_vars :: bind_free_vars))
              (cleaned_name_binds |> List.map fst |> SS.of_list)
          in
          { exp= ALetRec (new_name_binds, body_info.exp, ());
            is_pure= body_info.is_pure;
            free_vars }
  and helpC (cexp : 'c cexpr) : unit cexpr dce_info =
    match cexp with
    | CImmExpr imm ->
        let {exp; is_pure; free_vars} = helpI imm in
        make_info (CImmExpr exp) is_pure free_vars
    | CPrim1 (PrintStack, imm, _) ->
        let imm_info = helpI imm in
        { exp= CPrim1 (PrintStack, imm_info.exp, ());
          is_pure= false;
          free_vars= imm_info.free_vars }
    | CPrim1 (op, imm, _) ->
        let imm_info = helpI imm in
        { exp= CPrim1 (op, imm_info.exp, ());
          is_pure= imm_info.is_pure;
          free_vars= imm_info.free_vars }
    | CEPrim2 (op, lhs, rhs, _) ->
        let lhs_info = helpI lhs in
        let rhs_info = helpI rhs in
        { exp= CEPrim2 (op, lhs_info.exp, rhs_info.exp, ());
          is_pure= lhs_info.is_pure && rhs_info.is_pure;
          free_vars= SS.union lhs_info.free_vars rhs_info.free_vars }
    | CLPrim2 (op, lhs, rhs, _) ->
        let lhs_info = helpI lhs in
        let rhs_info = helpA rhs in
        { exp= CLPrim2 (op, lhs_info.exp, rhs_info.exp, ());
          is_pure= lhs_info.is_pure && rhs_info.is_pure;
          free_vars= SS.union lhs_info.free_vars rhs_info.free_vars }
    | CIf (cond, thn, els, _) ->
        let cond_info = helpI cond in
        let thn_info = helpA thn in
        let els_info = helpA els in
        let free_vars =
          union_sets
            [cond_info.free_vars; thn_info.free_vars; els_info.free_vars]
        in
        { exp= CIf (cond_info.exp, thn_info.exp, els_info.exp, ());
          is_pure= cond_info.is_pure && thn_info.is_pure && els_info.is_pure;
          free_vars }
    | CNativeApp (fname, args, _) ->
        let args_exps, _, args_fv = args |> List.map helpI |> split_infos in
        { exp= CNativeApp (fname, args_exps, ());
          is_pure= false;
          free_vars= union_sets args_fv }
    | CApp (func, args, _) ->
        let func_info = helpI func in
        let args_exps, _, args_fv = args |> List.map helpI |> split_infos in
        { exp= CApp (func_info.exp, args_exps, ());
          is_pure= false;
          free_vars= union_sets (func_info.free_vars :: args_fv) }
    | CTuple (elms, _) ->
        let elms_exps, elms_pure, elms_fv =
          elms |> List.map helpI |> split_infos
        in
        { exp= CTuple (elms_exps, ());
          is_pure= list_and elms_pure;
          free_vars= union_sets elms_fv }
    | CGetItem (tup, idx, _) ->
        let tup_info = helpI tup in
        let idx_info = helpI idx in
        { exp= CGetItem (tup_info.exp, idx_info.exp, ());
          is_pure= tup_info.is_pure && idx_info.is_pure;
          free_vars= SS.union tup_info.free_vars idx_info.free_vars }
    | CSetItem (tup, idx, newval, _) ->
        let tup_info = helpI tup in
        let idx_info = helpI idx in
        let newval_info = helpI newval in
        let free_vars =
          union_sets
            [tup_info.free_vars; idx_info.free_vars; newval_info.free_vars]
        in
        { exp= CSetItem (tup_info.exp, idx_info.exp, newval_info.exp, ());
          is_pure= false;
          free_vars }
    | CLambda (args, body, _, _) ->
        let body_info = helpA body in
        let new_fv = SS.diff body_info.free_vars (SS.of_list args) in
        { exp=
            CLambda
              ( args,
                body_info.exp,
                new_fv |> SS.elements |> List.sort String.compare,
                () );
          is_pure= true;
          free_vars= new_fv }
  in
  match p with
  | AProgram (body, _) -> AProgram ((helpA body).exp, ())
;;
