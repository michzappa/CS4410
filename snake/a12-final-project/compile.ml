open Anf
open Assembly
open Desugar
open Errors
open Exprs
open Phases
open Pretty
open Printf
open Utils
open Wellformed
open Environment
open Regalloc
open Dce
open Lift

let padding_value = 0xffffffffdeadbeefL

let const_true = 0xFFFFFFFFFFFFFFFFL

let const_false = 0x7FFFFFFFFFFFFFFFL

let bool_mask = 0x8000000000000000L

let bool_bit = 63L

let bool_tag = 0x000000000000000FL

let bool_tag_mask = 0x000000000000000FL

let num_tag = 0x0000000000000000L

let num_tag_mask = 0x0000000000000001L

let closure_tag = 0x0000000000000005L

let closure_tag_mask = 0x000000000000000FL

let tuple_tag = 0x0000000000000001L

let tuple_tag_mask = 0x000000000000000FL

let string_tag = 0x000000000000000BL

let string_tag_mask = 0x000000000000000FL

let const_nil = tuple_tag

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

let err_CALL_NOT_CLOSURE = 12L

let err_CALL_ARITY = 13L

let err_NOT_STRING = 14L

let err_CLOSURE_TO_STRING = 15L

let err_SLICE_LOW_INDEX = 16L

let err_SLICE_HIGH_INDEX = 17L

let err_STRING_NOT_BOOL = 18L

let err_NOT_INT = 19L

let err_PROGRAMMER_FAIL = 20L

let snake_entry_base_pointer = "snake_entry_base_pointer"

let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env
;;

(* Returns the stack-index (in words) of the deepest stack index used for any
   of the variables in this expression *)
let deepest_stack env =
  List.fold_right
    (fun (_, arg) deep_acc ->
      match arg with
      | RegOffset (offset, RBP) -> max deep_acc (offset / (-1 * word_size))
      | _ -> deep_acc )
    env 0
;;

(* Creates set of all registers used by the current function *)
let used_register env : reg list =
  List.fold_right
    (fun (_, arg) acc_regs ->
      match arg with
      | Reg r when List.mem r acc_regs -> r :: acc_regs
      | _ -> acc_regs )
    env []
;;

(* We picked tags for our outer environemnt so that we do not have to generate
   unique names for lambdas and the global program. This requires that
   naive_stack_allocation and compile_prog use the same tagged expression.
   Since that are called one after the other, this guarantees that the tags
   are consistent. *)
let naive_stack_allocation (prog : tag aprogram) :
    tag aprogram * arg name_envt tag_envt =
  let rec allocate_aexpr (expr : tag aexpr) (si : int) :
      arg name_envt * arg name_envt tag_envt =
    match expr with
    | ALet (name, bind, body, _) ->
        let bind_env, bind_closure_env = allocate_cexpr bind si in
        let binding_pair = (name, RegOffset (word_size * ~-si, RBP)) in
        let body_env, body_closure_env = allocate_aexpr body (si + 1) in
        ( bind_env @ [binding_pair] @ body_env,
          bind_closure_env @ body_closure_env )
    | ASeq (other, body, _) ->
        let other_env, other_closure_env = allocate_cexpr other si in
        let body_env, body_closure_env = allocate_aexpr body si in
        (other_env @ body_env, other_closure_env @ body_closure_env)
    | ACExpr expr -> allocate_cexpr expr si
    | ALetRec (bindings, body, _) ->
        let binding_env, binding_closure_env, si =
          List.fold_left
            (fun (acc_env, acc_closure_env, cur_si) (name, bind) ->
              let bind_env, bind_closure_env = allocate_cexpr bind cur_si in
              let bind_pair = (name, RegOffset (word_size * ~-cur_si, RBP)) in
              ( acc_env @ bind_env @ [bind_pair],
                acc_closure_env @ bind_closure_env,
                cur_si + 1 ) )
            ([], [], si) bindings
        in
        let body_env, body_closure_env = allocate_aexpr body si in
        (binding_env @ body_env, binding_closure_env @ body_closure_env)
  and allocate_cexpr (expr : tag cexpr) (si : int) :
      arg name_envt * arg name_envt tag_envt =
    match expr with
    | CIf (_, thn, els, _) ->
        let thn_env, thn_closure_env = allocate_aexpr thn si in
        let els_env, els_closure_env = allocate_aexpr els si in
        (thn_env @ els_env, thn_closure_env @ els_closure_env)
    | CLPrim2 (_, _, rhs, _) -> allocate_aexpr rhs si
    | CLambda (args, body, fvs, tag) ->
        (* Reserve stack space for free variables. *)
        let arg_env =
          List.mapi (fun i s -> (s, RegOffset (word_size * (i + 3), RBP))) args
        in
        let fv_env =
          List.mapi
            (fun i fv -> (fv, RegOffset (word_size * ~-(i + 1), RBP)))
            fvs
        in
        let body_env, body_closure_env =
          allocate_aexpr body (1 + List.length fvs)
        in
        let this_closure_env = arg_env @ fv_env @ body_env in
        let new_global_closure_env =
          (tag, this_closure_env) :: body_closure_env
        in
        ([], new_global_closure_env)
    | CROLambda (_, args, body, tag) ->
        (* Reserve stack space for free variables. *)
        let arg_env =
          List.mapi (fun i s -> (s, RegOffset (word_size * (i + 3), RBP))) args
        in
        let body_env, body_closure_env = allocate_aexpr body 1 in
        let this_closure_env = arg_env @ body_env in
        let new_global_closure_env =
          (tag, this_closure_env) :: body_closure_env
        in
        ([], new_global_closure_env)
    (* These all have immediate arguments, which have already been
       allocated if necessary. *)
    | CPrim1 (_, _, _)
     |CEPrim2 (_, _, _, _)
     |CNativeApp (_, _, _)
     |CApp (_, _, _)
     |CImmExpr _
     |CTuple (_, _)
     |CGetItem (_, _, _)
     |CSetItem (_, _, _, _) -> ([], [])
  in
  let allocate_env (prog : tag aprogram) : arg name_envt tag_envt =
    match prog with
    | AProgram (expr, _, tag) ->
        let fun_env, closure_envs = allocate_aexpr expr 1 in
        (tag, fun_env) :: closure_envs
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
           | ImmString _ -> ice "ImmString found in collect_arg_cycles"
           | ImmNum _ | ImmBool _ | ImmNil _ | ImmROId _ -> None
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

let heap_object_size_in_bytes (e : 'a cexpr) : int64 =
  match e with
  | CLambda (_, _, free_vars, _) ->
      (* [arity, code_ptr, #free_vars, free_vars...] *)
      let num_content_bytes = 3 + List.length free_vars in
      let num_padded_bytes = num_content_bytes + Int.rem num_content_bytes 2 in
      Int64.of_int (word_size * num_padded_bytes)
  | CTuple (elements, _) ->
      (* [header, elements..., padding] *)
      let tuple_size = List.length elements in
      let num_padded_bytes = 1 + tuple_size + Int.rem (tuple_size + 1) 2 in
      Int64.of_int (word_size * num_padded_bytes)
  | _ -> ice "Non-heap object passed to heap_object_size_in_bytes"
;;

let reserve (size : int64) (name : string) : instruction list =
  [ILineComment (sprintf "Reserving space for %s on the heap" name)]
  (* Spill allocated registers onto the stack so they are visible to GC. *)
  @ save_allocated_registers
  @ [ IMov (Reg (native_arg_reg 0), Const size);
      IMov (Reg (native_arg_reg 1), Reg RBP);
      IMov (Reg (native_arg_reg 2), Reg RSP);
      ICall (Label "try_gc") ]
  (* Restore allocated registers from the stack, with potentially
     changed values after GC. *)
  @ restore_allocated_registers
  @ [ILineComment "GC succeeded so we are guaranteed enough space"]
;;

let rec compile_fun
    (name : string)
    (args : string list)
    (free_vars : string list)
    (expr : tag aexpr)
    (env : arg name_envt)
    (global_env : arg name_envt tag_envt) :
    instruction list * instruction list * instruction list =
  let prelude = [ILabel name] in
  let stack_setup =
    let num_free_vars = List.length free_vars in
    (* If even, we increment num_vars to next even number (since we
       already use one slot for saved RBP). This ensures when a
       function call is made that it uses an even number of stack
       space to maintain alignment. *)
    let stack_slots = deepest_stack env in
    let needs_padding = Int.rem stack_slots 2 = 1 in
    let aligned_vars = stack_slots + if needs_padding then 1 else 0 in
    raise_if
      (Int.rem aligned_vars 2 != 0)
      (InternalCompilerError "aligned vars should always be even");
    let push_free_vars =
      (* Closure is passed arg at RBP + 16 *)
      [ ILineComment "Move closure from passed argument location to RAX";
        IMov (Reg RAX, RegOffset (word_size * 2, RBP)) ]
      @ flat_mapi
          (fun i fv ->
            let slot = List.assoc fv env in
            [ ILineComment "Move free variable out of closure into stack slot";
              IMov
                ( Reg R11,
                  RegOffset
                    ((word_size * (3 + i)) - Int64.to_int closure_tag, RAX) );
              IMov (slot, Reg R11) ] )
          free_vars
    in
    let stack_base_setup =
      [ IPush (Reg RBP);
        IMov (Reg RBP, Reg RSP);
        ISub (Reg RSP, Const (Int64.of_int (word_size * aligned_vars))) ]
    in
    (* Always pad the full stack since register allocation might
       cause any mix of free vars to local var placement. *)
    let push_padding =
      iota aligned_vars
      |> List.map (fun idx ->
             let offset = RegOffset (word_size * -(1 + idx), RBP) in
             IMov (Sized (QWORD_PTR, offset), HexConst padding_value) )
    in
    let maybe_push_free_vars =
      if num_free_vars > 0 then push_free_vars else []
    in
    stack_base_setup @ push_padding @ maybe_push_free_vars
  in
  let stack_teardown = [IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet] in
  let body = compile_aexpr expr env global_env args true in
  (prelude @ stack_setup, body, stack_teardown)

and compile_aexpr
    (e : tag aexpr)
    (env : arg name_envt)
    (global_env : arg name_envt tag_envt)
    (caller_args : string list)
    (is_tail : bool) : instruction list =
  match e with
  | ASeq (left, right, tag) ->
      let seq_name = sprintf "seq$#%d" tag in
      let lhs = compile_cexpr left env global_env caller_args false in
      let rhs = compile_aexpr right env global_env caller_args is_tail in
      [ ILineComment (sprintf "%s begin:" seq_name);
        ILineComment (sprintf "%s: executing lhs" seq_name) ]
      @ lhs
      @ [ILineComment (sprintf "%s: executing rhs" seq_name)]
      @ rhs
      @ [ILineComment (sprintf "%s end" seq_name)]
  | ALetRec (bindings, body, tag) ->
      let let_rec_name = sprintf "letrec$#%d" tag in
      let names, binds = List.split bindings in
      (* Invariant: the RHS of letrec bindings are lambdas. *)
      let move_insts =
        List.map
          (fun name ->
            [ ILineComment (sprintf "Moving %s onto stack" name);
              IMov (List.assoc name env, Reg RAX) ] )
          names
      in
      let bound_values : instruction list list =
        List.map
          (fun (name, cexp) ->
            ILineComment (sprintf "Function: %s" name)
            :: compile_cexpr cexp env global_env caller_args false )
          bindings
      in
      let compute_and_move_all =
        flat_mapi
          (fun i (compute_insts, move_ins) ->
            [ ILineComment
                (sprintf "%s: computing bound value %d" let_rec_name i) ]
            @ compute_insts @ move_ins )
          (List.combine bound_values move_insts)
      in
      let back_patch =
        binds
        |> List.map (fun lam ->
               match lam with
               | CLambda (_, _, fvs, _) -> fvs
               | CROLambda (_, _, _, _) -> []
               | _ -> ice "Compile found non-lambda let rec bind" )
        |> List.combine names
        |> List.map (fun (name, fvs) ->
               fvs |> enumerate
               |> List.filter (fun (_, fv) -> List.mem fv names)
               |> List.map (fun (idx, fv) ->
                      let offset_in_closure =
                        ((idx + 3) * word_size) - Int64.to_int closure_tag
                      in
                      [ IMov (Reg RAX, compile_imm (ImmId (name, 0)) env);
                        IMov (Reg R11, compile_imm (ImmId (fv, 0)) env);
                        IMov (RegOffset (offset_in_closure, RAX), Reg R11) ] )
               |> List.flatten )
        |> List.flatten
      in
      let body = compile_aexpr body env global_env caller_args is_tail in
      [ILineComment (sprintf "%s begin:" let_rec_name)]
      @ compute_and_move_all @ back_patch
      @ [ILineComment (sprintf "%s: executing body" let_rec_name)]
      @ body
      @ [ILineComment (sprintf "%s end" let_rec_name)]
  | ALet (bind_name, aexp, body, tag) ->
      let let_name, move_insts =
        ( sprintf "let$%s#%d" bind_name tag,
          [ ILineComment (sprintf "Moving %s onto stack" bind_name);
            IMov (List.assoc bind_name env, Reg RAX) ] )
      in
      let bound_value = compile_cexpr aexp env global_env caller_args false in
      let body = compile_aexpr body env global_env caller_args is_tail in
      [ ILineComment (sprintf "%s begin:" let_name);
        ILineComment (sprintf "%s: computing bound value" let_name) ]
      @ bound_value @ move_insts
      @ [ILineComment (sprintf "%s: executing let body" let_name)]
      @ body
      @ [ILineComment (sprintf "%s end:" let_name)]
  | ACExpr e -> compile_cexpr e env global_env caller_args is_tail

and compile_cexpr
    (e : tag cexpr)
    (env : arg name_envt)
    (global_env : arg name_envt tag_envt)
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
      IJne (Label err_label);
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
      IJne (Label err_label);
      (* Check if the argument is the nil constant *)
      ICmp (Reg R11, HexConst const_nil);
      (* If argument is nil, error *)
      IJe (Label nil_label);
      ILineComment (sprintf "Done checking %s for tuple-ness" (r_to_asm reg)) ]
  in
  let num_check_reg reg err_name =
    let err_label = sprintf "error_%s_not_number" err_name in
    [ ILineComment (sprintf "Checking %s for number-ness" (r_to_asm reg));
      IMov (Reg R11, Reg reg);
      (* Bitwise AND with the flag mask and observe the result *)
      ITest (Reg R11, HexConst num_tag_mask);
      (* Since num_tag is 0x0, error if result was non-zero *)
      IJnz (Label err_label);
      ILineComment (sprintf "Done checking %s for number-ness" (r_to_asm reg))
    ]
  in
  let closure_check_reg reg =
    let err_label = "error_call_not_closure" in
    [ ILineComment (sprintf "Checking %s for closure-ness" (r_to_asm reg));
      IMov (Reg R11, Reg reg);
      (* Get relevant bits of closure type tag *)
      IAnd (Reg R11, HexConst closure_tag_mask);
      (* Check whether they match the closure type tag *)
      ICmp (Reg R11, HexConst closure_tag);
      (* Re-load from source reg after clobbering R11 *)
      IMov (Reg R11, Reg reg);
      (* If argument isn't a tuple, error *)
      IJne (Label err_label);
      ILineComment (sprintf "Done checking %s for closure-ness" (r_to_asm reg))
    ]
  in
  let check_arity_reg reg given_arity =
    let err_label = "error_call_arity" in
    [ ILineComment
        (sprintf "Checking %s with given arity of %d" (r_to_asm reg) given_arity);
      (* Compare index against arity *)
      ICmp
        ( Sized (QWORD_PTR, RegOffset (~-(Int64.to_int closure_tag), RAX)),
          Const (Int64.of_int given_arity) );
      (* Jump to error if closure's arity is not equal to given arity *)
      IJne (Label err_label);
      ILineComment (sprintf "Done checking %s for arity" (r_to_asm reg)) ]
  in
  let idx_low_check_reg =
    let err_label = "error_access_low_index" in
    [ ILineComment (sprintf "Checking %s for index low-ness" (r_to_asm R11));
      (* Compare index against zero *)
      ICmp (Reg R11, Const 0L);
      (* Jump to error if R11 is less than zero *)
      IJl (Label err_label);
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
      IJge (Label err_label);
      ILineComment
        (sprintf "Done checking %s for index high-ness" (r_to_asm R11)) ]
  in
  match e with
  | CLambda (params, body, fvs, tag) ->
      let lambda_name = sprintf "lambda$%d" tag in
      let lambda_done = sprintf "lambda_done$%d" tag in
      let fun_env = List.assoc tag global_env in
      let func_prelude, func_body, func_teardown =
        compile_fun lambda_name params fvs body fun_env global_env
      in
      let lambda_size_bytes = heap_object_size_in_bytes e in
      let allocate_lambda = reserve lambda_size_bytes lambda_name in
      let move_lambda_data =
        [ ILineComment "Setting lambda metadata";
          ILineComment "Setting arity";
          IMov
            ( Sized (QWORD_PTR, RegOffset (0, RAX)),
              Const (Int64.of_int (List.length params)) );
          ILineComment "Setting code pointer";
          ILea (Reg R11, RelLabelContents lambda_name);
          IMov (Sized (QWORD_PTR, RegOffset (word_size, RAX)), Reg R11);
          ILineComment "Setting # of free vars";
          IMov
            ( Sized (QWORD_PTR, RegOffset (2 * word_size, RAX)),
              Const (Int64.of_int (List.length fvs)) );
          ILineComment "Setting free vars values" ]
        @ flat_mapi
            (fun i fv ->
              [ ILineComment (sprintf "Setting free var %s" fv);
                IMov (Reg R11, compile_imm (ImmId (fv, 0)) env);
                IMov (RegOffset (word_size * (3 + i), RAX), Reg R11) ] )
            fvs
      in
      let maybe_padding =
        let num_fvs = List.length fvs in
        if Int.rem num_fvs 2 = 0 then
          let offset = RegOffset (word_size * (3 + num_fvs), RAX) in
          [IMov (Sized (QWORD_PTR, offset), HexConst padding_value)]
        else
          []
      in
      let tag_lambda_pointer =
        [ ILineComment "Tagging lambda pointer";
          IOr (Reg RAX, HexConst closure_tag) ]
      in
      [IJmp (Label lambda_done)] @ func_prelude @ func_body @ func_teardown
      @ [ILabel lambda_done] @ allocate_lambda @ move_lambda_data
      @ maybe_padding @ tag_lambda_pointer
  | CROLambda (name, params, body, tag) ->
      let lambda_name = sprintf "%s$func" name in
      let lambda_done = sprintf "%s$func_done" name in
      let fun_env = List.assoc tag global_env in
      let func_prelude, func_body, func_teardown =
        compile_fun lambda_name params [] body fun_env global_env
      in
      let load_rolambda_pointer =
        [ ILineComment "Load the RO Lambda";
          IMov (Reg RAX, LabelOffset (name, closure_tag)) ]
      in
      [IJmp (Label lambda_done)] @ func_prelude @ func_body @ func_teardown
      @ [ILabel lambda_done] @ load_rolambda_pointer
  | CImmExpr e -> [IMov (Reg RAX, compile_imm e env)]
  | CPrim1 (((Add1 | Sub1) as op), n, tag) ->
      let prim1_name = sprintf "prim1$%s#%d" (name_of_op1 op) tag in
      let n_arg = compile_imm n env in
      let op_inst =
        match op with
        | Add1 -> IAdd (Reg RAX, Const 2L)
        | Sub1 -> ISub (Reg RAX, Const 2L)
        | _ -> ice "invalid op in nested match"
      in
      [ ILineComment (sprintf "%s begin:" prim1_name);
        (* Move in the argument *)
        IMov (Reg RAX, n_arg) ]
      @ num_check_reg RAX "arith"
      @ [ (* Perform operation *)
          op_inst;
          (* After the operation was performed, check for overflow *)
          IJo (Label "error_overflow");
          ILineComment (sprintf "%s end:" prim1_name) ]
  | CPrim1 (((IsBool | IsNum | IsTuple | IsClosure | IsString) as op), x, tag)
    ->
      let prim1_name = sprintf "prim1$%s#%d" (name_of_op1 op) tag in
      let done_label = sprintf "done_%d" tag in
      let x_arg = compile_imm x env in
      let tag_mask, tag =
        match op with
        | IsBool -> (bool_tag_mask, bool_tag)
        | IsNum -> (num_tag_mask, num_tag)
        | IsTuple -> (tuple_tag_mask, tuple_tag)
        | IsClosure -> (closure_tag_mask, closure_tag)
        | IsString -> (string_tag_mask, string_tag)
        | _ -> ice "invalid op in nested match"
      in
      [ ILineComment (sprintf "%s begin:" prim1_name);
        (* Move in the argument *)
        IMov (Reg RAX, x_arg);
        (* Get relevant bits of type tag *)
        IAnd (Reg RAX, HexConst tag_mask);
        (* Check whether they match the type tag *)
        ICmp (Reg RAX, HexConst tag);
        (* Pre-load true, expecting success *)
        IMov (Reg RAX, HexConst const_true);
        (* If success, we are done *)
        IJe (Label done_label);
        (* If not success, load false and be done *)
        IMov (Reg RAX, HexConst const_false);
        ILabel done_label;
        ILineComment (sprintf "%s end:" prim1_name) ]
  | CPrim1 (Not, b, tag) ->
      let prim1_name = sprintf "prim1$%s#%d" (name_of_op1 Not) tag in
      let n_arg = compile_imm b env in
      [ ILineComment (sprintf "%s begin:" prim1_name);
        (* Load the argument *)
        IMov (Reg RAX, n_arg) ]
      (* Value check the argument *)
      @ bool_check_reg RAX "logic"
      (* Flip the bit for bool *)
      @ [ IBtc (Reg RAX, Const bool_bit);
          ILineComment (sprintf "%s end:" prim1_name) ]
  | CPrim1 (PrintStack, x, tag) ->
      let prim1_name = sprintf "prim1$%s#%d" (name_of_op1 PrintStack) tag in
      let x_arg = compile_imm x env in
      [ILineComment (sprintf "%s begin:" prim1_name)]
      @ save_allocated_registers
      @ [ (* Set up arguments *)
          IMov (Reg (native_arg_reg 0), x_arg);
          IMov (Reg (native_arg_reg 1), Reg RSP);
          IMov (Reg (native_arg_reg 2), Reg RBP);
          (* Call method with no cleanup necessary after *)
          ICall (Label "print_stack") ]
      @ restore_allocated_registers
      @ [ILineComment (sprintf "%s end:" prim1_name)]
  | CLPrim2 (((And | Or) as op), lhs, rhs, tag) ->
      let prim2_name = sprintf "prim2$%s#%d" (name_of_lop2 op) tag in
      let done_label = sprintf "done_%d" tag in
      let lhs_arg = compile_imm lhs env in
      let rhs_insts = compile_aexpr rhs env global_env caller_args false in
      let jmp_inst =
        match op with
        (* Jump when LHS is false so that AND results in false *)
        | And -> IJne (Label done_label)
        (* Jump when LHS is true so that OR results in true *)
        | Or -> IJe (Label done_label)
      in
      [ ILineComment (sprintf "%s begin:" prim2_name);
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
      @ [ILabel done_label; ILineComment (sprintf "%s end:" prim2_name)]
  | CEPrim2 (((Plus | Minus | Times) as op), lhs, rhs, tag) ->
      let prim2_name = sprintf "prim2$%s#%d" (name_of_eop2 op) tag in
      let lhs_arg = compile_imm lhs env in
      let rhs_arg = compile_imm rhs env in
      let insts =
        match op with
        | Plus -> [IAdd (Reg RAX, Reg R11)]
        | Minus -> [ISub (Reg RAX, Reg R11)]
        | Times -> [ISar (Reg RAX, Const 1L); IMul (Reg RAX, Reg R11)]
        | _ -> ice "invalid op in nested match"
      in
      (* Load lhs *)
      [ILineComment (sprintf "%s begin:" prim2_name); IMov (Reg RAX, lhs_arg)]
      @ num_check_reg RAX "arith"
      (* Load rhs into R11 for checking *)
      @ [IMov (Reg R11, rhs_arg)]
      @ num_check_reg R11 "arith"
      (* Perform computation on RAX and R11 *)
      @ insts
      @ [ (* After the operation was performed, check for overflow *)
          IJo (Label "error_overflow");
          ILineComment (sprintf "%s end:" prim2_name) ]
  | CEPrim2 (Eq, lhs, rhs, tag) ->
      let prim2_name = sprintf "prim2$%s#%d" (name_of_eop2 Eq) tag in
      let done_label = sprintf "done_%d" tag in
      let lhs_arg = compile_imm lhs env in
      let rhs_arg = compile_imm rhs env in
      [ ILineComment (sprintf "%s begin:" prim2_name);
        (* Load lhs for comparison *)
        IMov (Reg RAX, lhs_arg);
        (* Load rhs for comparison *)
        IMov (Reg R11, rhs_arg);
        (* Compare lhs to rhs *)
        ICmp (Reg RAX, Reg R11);
        (* Pre-load true *)
        IMov (Reg RAX, HexConst const_true);
        (* If lhs == rhs, we are done *)
        IJe (Label done_label);
        (* If lhs != rhs, load false and be done *)
        IMov (Reg RAX, HexConst const_false);
        ILabel done_label;
        ILineComment (sprintf "%s end:" prim2_name) ]
  | CEPrim2 (((Greater | GreaterEq | Less | LessEq) as op), lhs, rhs, tag) ->
      let prim2_name = sprintf "prim2$%s#%d" (name_of_eop2 op) tag in
      let done_label = sprintf "done_%d" tag in
      let lhs_arg = compile_imm lhs env in
      let rhs_arg = compile_imm rhs env in
      let jump_inst =
        match op with
        | Greater -> IJg (Label done_label)
        | GreaterEq -> IJge (Label done_label)
        | Less -> IJl (Label done_label)
        | LessEq -> IJle (Label done_label)
        | _ -> ice "invalid op in nested match"
      in
      [ ILineComment (sprintf "%s begin:" prim2_name);
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
          ILineComment (sprintf "%s end:" prim2_name) ]
  | CIf (cond, thn, els, tag) ->
      let if_name = sprintf "if#%d" tag in
      let else_label = sprintf "else_%d" tag in
      let done_label = sprintf "done_%d" tag in
      let c_arg = compile_imm cond env in
      let thn_comp = compile_aexpr thn env global_env caller_args is_tail in
      let els_comp = compile_aexpr els env global_env caller_args is_tail in
      [ ILineComment (sprintf "%s begin:" if_name);
        ILineComment (sprintf "%s condition check:" if_name);
        (* Load condition and check boolean-ness *)
        IMov (Reg RAX, c_arg) ]
      @ bool_check_reg RAX "if"
      (* Check if condition is true, if not jump to else *)
      @ [ ICmp (Reg RAX, HexConst const_true);
          IJne (Label else_label);
          ILineComment (sprintf "%s then branch:" if_name) ]
      (* Evaluate then and and jump to done *)
      @ thn_comp
      @ [ IJmp (Label done_label);
          (* Evaluate else branch and be done *)
          ILineComment (sprintf "%s else branch:" if_name);
          ILabel else_label ]
      @ els_comp
      @ [ILabel done_label; ILineComment (sprintf "%s end:" if_name)]
  | CTuple (immexprs, tag) ->
      let tuple_name = sprintf "tuple#%d" tag in
      let tuple_size = List.length immexprs in
      let tuple_size_bytes = heap_object_size_in_bytes e in
      let allocate_tuple = reserve tuple_size_bytes tuple_name in
      let move_tuple_size =
        (* Tuple size is stored as a "normal" number and not a snake
           number. *)
        [ ILineComment "Setting tuple size";
          IMov (Reg R11, Const (Int64.of_int tuple_size));
          IMov (RegOffset (0, RAX), Reg R11) ]
      in
      let move_tuple_items =
        ILineComment "Moving tuple contents onto heap"
        :: flat_mapi
             (fun idx expr ->
               [ IMov (Reg R11, compile_imm expr env);
                 IMov (RegOffset (word_size * (idx + 1), RAX), Reg R11) ] )
             immexprs
      in
      let maybe_padding =
        if Int.rem tuple_size 2 = 0 then
          let offset = RegOffset (word_size * (1 + tuple_size), RAX) in
          [IMov (Sized (QWORD_PTR, offset), HexConst padding_value)]
        else
          []
      in
      let tag_tuple_pointer =
        [ILineComment "Tagging tuple pointer"; IOr (Reg RAX, HexConst tuple_tag)]
      in
      [ILineComment (sprintf "Tuple %s begin" tuple_name)]
      @ allocate_tuple @ move_tuple_size @ move_tuple_items @ maybe_padding
      @ tag_tuple_pointer
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
  | CApp (func, app_exprs, tag)
  (* Tail-recursive application for a function defined in snake, all
     arguments go on stack *)
    when is_tail && List.length app_exprs <= List.length caller_args ->
      let app_name = sprintf "tail_app%s#%d" (string_of_immexpr func) tag in
      let app_args_len = List.length app_exprs in
      let closure_arg = compile_imm func env in
      let load_closure = [IMov (Reg RAX, closure_arg)] in
      let check_closure =
        closure_check_reg RAX @ check_arity_reg R11 app_args_len
      in
      (* We are save to replace the closure since the free vars are already
         pushed onto the stack so no need to access the old closure *)
      let move_closure_onto_stack =
        [IMov (RegOffset (2 * word_size, RBP), Reg RAX)]
      in
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
            | [] -> ice "encountered empty cycle"
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
                  flat_map
                    (fun (idx, (name, tag)) ->
                      [ IMov (Reg R11, compile_imm (ImmId (name, tag)) env);
                        IMov (RegOffset (word_size * (3 + idx), RBP), Reg R11)
                      ] )
                    rest
                in
                (* The value in the scratch register is then placed on
                   the stack after everything else has been *)
                let restore_cycle_break =
                  [IMov (RegOffset (word_size * (3 + index), RBP), Reg RAX)]
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
        flat_map
          (fun (idx, arg) ->
            [ IMov (Reg R11, compile_imm arg env);
              IMov (RegOffset (word_size * (3 + idx), RBP), Reg R11) ] )
          non_cycle_args
      in
      [ILineComment (sprintf "Tail App %s begin:" app_name)]
      @ load_closure @ check_closure @ move_closure_onto_stack
      (* Arguments for the tail-call *)
      @ cycle_insts
      @ moving_non_cycle_args
      @ [ (* Move closure back into RAX *)
          IMov (Reg RAX, RegOffset (word_size * 2, RBP));
          (* Reclaim the stack space used for local variables since it
             is set up again after the tail_entry *)
          IMov (Reg RSP, Reg RBP);
          IPop (Reg RBP);
          IJmp (RegOffset (word_size - Int64.to_int closure_tag, RAX));
          ILineComment (sprintf "Tail App %s end:" app_name) ]
  | CApp (func, args, tag) ->
      (* Non-tail-recursive application for a function defined in
         snake, all arguments go on stack *)
      let app_name = sprintf "app%s#%d" (string_of_immexpr func) tag in
      let app_args_len = List.length args in
      let closure_arg = compile_imm func env in
      let load_closure = [IMov (Reg RAX, closure_arg)] in
      let check_closure =
        closure_check_reg RAX @ check_arity_reg R11 app_args_len
      in
      let padding_inst, padding_amount =
        (* Plus one to account for lambda itself *)
        if Int.rem (app_args_len + 1) 2 = 0 then
          (ILineComment "no padding needed before call", 0)
        else
          (IPush (HexConst padding_value), 1)
      in
      let push_args_onto_stack =
        flat_rev_map
          (fun a -> [IMov (Reg R11, compile_imm a env); IPush (Reg R11)])
          args
      in
      let push_closure_onto_stack =
        [IMov (Reg RAX, closure_arg); IPush (Reg RAX)]
      in
      let stack_slot_usage = 1 + app_args_len + padding_amount in
      [ILineComment (sprintf "App %s begin:" app_name)]
      @ save_allocated_registers @ load_closure @ check_closure @ [padding_inst]
      @ push_args_onto_stack @ push_closure_onto_stack
      @ [ ICall (RegOffset (word_size - Int64.to_int closure_tag, RAX));
          (* Reclaim the stack space used for local variables *)
          IAdd (Reg RSP, Const (Int64.of_int (word_size * stack_slot_usage))) ]
      @ restore_allocated_registers
      @ [ILineComment (sprintf "App %s end:" app_name)]
  | CNativeApp (fname, args, tag) ->
      (* Application of a function defined in the C runtime, arguments
         follow C calling convention *)
      let app_name = sprintf "Native %s#%d" fname tag in
      let is_func_allocating = List.mem fname allocating_native_functions in
      let arged_args = List.map (fun arg -> compile_imm arg env) args in
      let arged_args =
        (* Adding RSP and RBP to the native function's arguments if it
           can possibly allocate, as they are needed in the
           runtime. *)
        if is_func_allocating then (* RAX is a proxy for saved RSP *)
          arged_args @ [Reg RAX; Reg RBP]
        else
          arged_args
      in
      let maybe_save_rsp =
        if is_func_allocating then [IMov (Reg RAX, Reg RSP)] else []
      in
      let args_in_reg, args_on_stack = split_at 6 arged_args in
      let args_in_reg_inst =
        List.mapi
          (fun idx arg -> IMov (Reg (native_arg_reg idx), arg))
          args_in_reg
      in
      let stack_args_len = List.length args_on_stack in
      let padding_inst, padding_amount =
        if Int.rem stack_args_len 2 = 0 then
          (ILineComment "no padding needed before call", 0)
        else
          (IPush (HexConst padding_value), 1)
      in
      let push_args_onto_stack =
        flat_rev_map
          (fun arg -> [IMov (Reg R11, arg); IPush (Reg R11)])
          args_on_stack
      in
      let stack_slot_usage = stack_args_len + padding_amount in
      let stack_arg_cleanup =
        if stack_args_len > 0 then
          IAdd (Reg RSP, Const (Int64.of_int (word_size * stack_slot_usage)))
        else
          ILineComment "No arguments on the stack"
      in
      [ILineComment (sprintf "App %s begin:" app_name)]
      @ save_allocated_registers
      (* Save RSP into RAX if this function needs RSP *)
      @ maybe_save_rsp
      (* Set up argument in registers *)
      @ args_in_reg_inst
      (* Place stack padding if necessary *)
      @ [padding_inst]
      (* Set up arguments on the stack *)
      @ push_args_onto_stack
      @ [ (* Call method with cleanup afterwards *)
          ICall (Label fname);
          (* Cleanup stack if necessary *)
          stack_arg_cleanup ]
      @ restore_allocated_registers
      @ [ILineComment (sprintf "App %s end:" app_name)]

and compile_imm (e : tag immexpr) (env : arg name_envt) : arg =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> HexConst const_true
  | ImmBool (false, _) -> HexConst const_false
  | ImmId (x, _) -> List.assoc x env
  | ImmNil _ -> HexConst const_nil
  | ImmString _ -> ice "ImmString in compile_imm"
  | ImmROId (s, ROString, _) -> LabelOffset (s, string_tag)
  | ImmROId (s, ROTuple, _) -> LabelOffset (s, tuple_tag)
;;

let compile_prog ((anfed : tag aprogram), (global_env : arg name_envt tag_envt))
    : string =
  match anfed with
  | AProgram (expr, read_onlys, tag) ->
      (* Declare code section, runtime function names, and runtime global
         variables. Must match C code names. *)
      let prelude =
        [ ISection ".note.GNU-stack";
          ISection ".text";
          ILineComment "run-time C functions" ]
        @ List.map (fun (n, _) -> IExtern n) native_fun_env
        @ List.map (fun n -> IExtern n) hidden_native_functions
        @ [IExtern snake_entry_base_pointer]
      in
      (* Error routines that call non-returning error C function *)
      let error_routines =
        let error_routine (name : string) (code : int64) (reg : reg) =
          [ ILineComment "never returning sub-routine";
            ILabel (sprintf "error_%s" name);
            IMov (Reg RDI, HexConst code);
            IMov (Reg RSI, Reg reg);
            ICall (Label "error");
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
        (* Semantic checks *)
        @ error_routine "access_low_index" err_ACCESS_LOW_INDEX RAX
        @ error_routine "access_high_index" err_ACCESS_HIGH_INDEX RAX
        @ error_routine "call_not_closure" err_CALL_NOT_CLOSURE RAX
        @ error_routine "call_arity" err_CALL_ARITY RAX
        (* Register does not matter in this error case *)
        @ error_routine "out_of_memory" err_OUT_OF_MEMORY RAX
      in
      let expr_code =
        let setup, body, teardown =
          compile_fun "our_code_starts_here$actual" [] [] expr
            (List.assoc tag global_env)
            global_env
        in
        let new_setup =
          match setup with
          | (ILabel "our_code_starts_here$actual" as i_label)
            :: (IPush (Reg RBP) as i_save_rbp)
            :: (IMov (Reg RBP, Reg RSP) as i_rsp_into_rbp)
            :: (ISub (Reg RSP, Const _) as i_reserve_locals)
            :: rest ->
              [ i_label;
                i_save_rbp;
                i_rsp_into_rbp;
                i_reserve_locals;
                IMov (RelLabelContents snake_entry_base_pointer, Reg RBP) ]
              @ rest
          | _ ->
              ice
                "Compilation of our_code_starts_here did not produce global \
                 then label at the front"
        in
        new_setup @ body @ teardown
      in
      (* Rather then directly going into the code we have a trampoline
         sets up some of the necessary snake runtime *)
      let trampoline =
        (* Pad callee saved register if necessary to keep stack alignment *)
        let callee_saved_regs =
          if Int.rem (List.length callee_saved_regs) 2 = 1 then
            R11 :: callee_saved_regs
          else
            callee_saved_regs
        in
        (* Function label and setup *)
        [ IGlobal "our_code_starts_here";
          ILabel "our_code_starts_here";
          IPush (Reg RBP);
          IMov (Reg RBP, Reg RSP) ]
        (* Store the callee saved registers *)
        @ List.map (fun r -> IPush (Reg r)) callee_saved_regs
        (* Call actual code*)
        @ [ICall (Label "our_code_starts_here$actual")]
        (* Restore the callee saved registers *)
        @ List.rev_map (fun r -> IPop (Reg r)) callee_saved_regs
        (* Clean up function and return *)
        @ [IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet]
      in
      let data_section =
        flat_map
          (fun (ro, name) ->
            ILabel name
            ::
            ( match ro with
            | String s ->
                [ IDataNumber (Int64.of_int (String.length s));
                  IDataLabel (name, word_size * 2);
                  IDataBytes (String.escaped s) ]
            | EmptyTuple -> [IDataNumber 0L; IDataNumber padding_value]
            | EmptyFvLambda arg_cnt ->
                [ IDataNumber (Int64.of_int arg_cnt);
                  IDataLabel (sprintf "%s$func" name, 0);
                  IDataNumber 0L;
                  IDataNumber padding_value ] ) )
          read_onlys
      in
      let full_inst_list =
        prelude @ expr_code @ error_routines @ trampoline @ data_section
      in
      to_asm full_inst_list
;;

let run_if should_run f = if should_run then f else no_op_phase

let pick_alloc_strategy (strat : alloc_strategy) =
  match strat with
  | Naive -> naive_stack_allocation
  | Register -> register_allocation
;;

let compile_to_string
    ?(no_builtins = false)
    ?(no_dce = false)
    (alloc_strat : alloc_strategy)
    (prog : sourcespan program pipeline) : string pipeline =
  prog
  (* un-interpolate strings into concatenations before well_formed *)
  (* this might error on invalid string formatting *)
  |> add_phase desugared_interpolations desugar_interpolations
  |> add_err_phase well_formed is_well_formed
  |> add_phase untagged untagP
  |> add_phase desugared desugar
  |> run_if (not no_builtins) (add_phase add_natives add_native_lambdas)
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> run_if (not no_dce)
       (add_phase dceed (fun p -> atag (dead_code_elimination p)))
  (* lift all read only data and replace with stand-ins *)
  |> add_phase lifted lift_read_only
  |> add_phase locate_bindings (pick_alloc_strategy alloc_strat)
  |> add_phase result compile_prog
;;
