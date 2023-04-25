open Asm
open Errors
open Exprs
open Phases
open Pretty
open Printf

let is_imm (e : 'a expr) : bool =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | EPrim1 _ | EPrim2 _ | ELet _ | EIf _ -> false
;;

let rec is_anf (e : 'a expr) : bool =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | EPrim1 (_, e, _) -> is_imm e
  | EPrim2 ((And | Or), e1, e2, _) -> is_imm e1 && is_anf e2
  | EPrim2 (_, e1, e2, _) -> is_imm e1 && is_imm e2
  | EIf (cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | ELet (binds, body, _) ->
      List.for_all (fun (_, e, _) -> is_anf e) binds && is_anf body
;;

let const_true = 0xFFFFFFFFFFFFFFFFL

let const_false = 0x7FFFFFFFFFFFFFFFL

let bool_mask = 0x8000000000000000L

let bool_bit = 63L

let bool_tag = 0x0000000000000007L

let bool_tag_mask = 0x0000000000000007L

let num_tag = 0x0000000000000000L

let num_tag_mask = 0x0000000000000001L

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let check_scope (e : sourcespan expr) : sourcespan expr fallible =
  let ecf e = e |> err_concat |> Result.map (Fun.const []) in
  let rec help e env : unit list fallible =
    match e with
    | EBool _ -> Ok []
    | ENumber (n, loc)
      when n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L ->
        Error
          [ LanguageLimitationError
              (sprintf "Integer '%Ld' out of range at %s" n
                 (string_of_sourcespan loc) ) ]
    | ENumber _ -> Ok []
    | EId (x, loc) -> (
      try List.assoc x env |> ignore |> Fun.const (Ok [])
      with Not_found ->
        Error
          [ BindingError
              (sprintf "The identifier %s, used at <%s>, is not in scope" x
                 (string_of_sourcespan loc) ) ] )
    | EPrim1 (_, e, _) -> help e env
    | EPrim2 (_, l, r, _) -> ecf [help l env; help r env]
    | EIf (c, t, f, _) -> ecf [help c env; help t env; help f env]
    | ELet (binds, body, _) ->
        let binds_res, env2, _ =
          let process (prev_results, scope_env, shadow_env) (x, e, loc) =
            let bind_res =
              try
                let existing = List.assoc x shadow_env in
                Error
                  [ BindingError
                      (sprintf
                         "The identifier %s, defined at <%s>, shadows one \
                          defined at <%s>"
                         x (string_of_sourcespan loc)
                         (string_of_sourcespan existing) ) ]
              with Not_found -> help e scope_env
            in
            ( ecf [prev_results; bind_res],
              (x, loc) :: scope_env,
              (x, loc) :: shadow_env )
          in
          List.fold_left process (Ok [], env, []) binds
        in
        ecf [binds_res; help body env2]
  in
  Result.map (Fun.const e) (help e [])
;;

let rec desugar (e : 'a expr) : 'a expr =
  match e with
  | (ENumber _ | EBool _ | EId _) as dexpr -> dexpr
  | EPrim1 (op, arg, a) -> EPrim1 (op, desugar arg, a)
  | EPrim2 (op, lhs, rhs, a) -> EPrim2 (op, desugar lhs, desugar rhs, a)
  | EIf (c, t, f, a) -> EIf (desugar c, desugar t, desugar f, a)
  | ELet (bindings, body, a) ->
      let bindings =
        List.map (fun (name, bind, a) -> (name, desugar bind, a)) bindings
      in
      let body = desugar body in
      ELet (bindings, body, a)
;;

let rec find (ls : (string * 'a) list) (x : string) : 'a =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

let rename (e : tag expr) : tag expr =
  let rec rename_help (env : (string * string) list) (e : tag expr) =
    let rename_env = rename_help env in
    match e with
    | ENumber (_, _) | EBool (_, _) -> e
    | EPrim1 (op, body, tag) -> EPrim1 (op, rename_env body, tag)
    | EPrim2 (op, l, r, tag) -> EPrim2 (op, rename_env l, rename_env r, tag)
    | EIf (c, t, f, tag) -> EIf (rename_env c, rename_env t, rename_env f, tag)
    | EId (name, tag) -> EId (find env name, tag)
    | ELet (binds, body, tag) ->
        let rename_bind (acc_binds, acc_env) (name, binding, tag) =
          let new_name = sprintf "%s#%d" name tag in
          let new_binding = rename_help acc_env binding in
          ( (new_name, new_binding, tag) :: acc_binds,
            (name, new_name) :: acc_env )
        in
        let binds, new_env = List.fold_left rename_bind ([], env) binds in
        let binds = List.rev binds in
        ELet (binds, rename_help new_env body, tag)
  in
  rename_help [] e
;;

let tag (e : 'a expr) : tag expr =
  let rec help (e : 'a expr) (num : int) : tag expr * tag =
    match e with
    | EId (x, _) -> (EId (x, num), num + 1)
    | ENumber (n, _) -> (ENumber (n, num), num + 1)
    | EBool (b, _) -> (EBool (b, num), num + 1)
    | EPrim1 (op, e, _) ->
        let tag_e, new_n = help e (num + 1) in
        (EPrim1 (op, tag_e, num), new_n)
    | EPrim2 (op, e1, e2, _) ->
        let tag_e1, num_e1 = help e1 (num + 1) in
        let tag_e2, num_e2 = help e2 num_e1 in
        (EPrim2 (op, tag_e1, tag_e2, num), num_e2)
    | ELet (binds, body, _) ->
        let new_binds, num_binds =
          List.fold_left
            (fun (rev_binds, next_num) (x, b, _) ->
              let tag_b, num_b = help b (next_num + 1) in
              ((x, tag_b, next_num) :: rev_binds, num_b) )
            ([], num + 1)
            binds
        in
        let tag_body, num_body = help body num_binds in
        (ELet (List.rev new_binds, tag_body, num), num_body)
    | EIf (cond, thn, els, _) ->
        let tag_cond, num_cond = help cond (num + 1) in
        let tag_thn, num_thn = help thn num_cond in
        let tag_els, num_els = help els num_thn in
        (EIf (tag_cond, tag_thn, tag_els, num), num_els)
  in
  let ans, _ = help e 1 in
  ans
;;

let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId (x, _) -> EId (x, ())
  | ENumber (n, _) -> ENumber (n, ())
  | EBool (b, _) -> EBool (b, ())
  | EPrim1 (op, e, _) -> EPrim1 (op, untag e, ())
  | EPrim2 (op, e1, e2, _) -> EPrim2 (op, untag e1, untag e2, ())
  | ELet (binds, body, _) ->
      ELet (List.map (fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf (cond, thn, els, _) -> EIf (untag cond, untag thn, untag els, ())
;;

let anf (e : tag expr) : unit expr =
  let rec helpC (e : tag expr) : unit expr * (string * unit expr) list =
    match e with
    | ENumber (n, _) -> (ENumber (n, ()), [])
    | EBool (b, _) -> (EBool (b, ()), [])
    | EId (name, _) -> (EId (name, ()), [])
    | EPrim1 (op, arg, _) ->
        let arg_imm, arg_setup = helpI arg in
        (EPrim1 (op, arg_imm, ()), arg_setup)
    | EPrim2 (((And | Or) as op), lhs, rhs, _) ->
        let lhs_imm, lhs_setup = helpI lhs in
        (EPrim2 (op, lhs_imm, anf rhs, ()), lhs_setup)
    | EPrim2 (op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (EPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf (cond, _then, _else, _) ->
        let cond_imm, cond_setup = helpI cond in
        (EIf (cond_imm, anf _then, anf _else, ()), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
  and helpI (e : tag expr) : unit expr * (string * unit expr) list =
    match e with
    | ENumber (n, _) -> (ENumber (n, ()), [])
    | EBool (b, _) -> (EBool (b, ()), [])
    | EId (name, _) -> (EId (name, ()), [])
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (EId (tmp, ()), arg_setup @ [(tmp, EPrim1 (op, arg_imm, ()))])
    | EPrim2 (((And | Or) as op), lhs, rhs, tag) ->
        let tmp = sprintf "binop_log_%d" tag in
        let lhs_imm, lhs_setup = helpI lhs in
        (EId (tmp, ()), lhs_setup @ [(tmp, EPrim2 (op, lhs_imm, anf rhs, ()))])
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( EId (tmp, ()),
          left_setup @ right_setup
          @ [(tmp, EPrim2 (op, left_imm, right_imm, ()))] )
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        ( EId (tmp, ()),
          cond_setup @ [(tmp, EIf (cond_imm, anf _then, anf _else, ()))] )
    | ELet ([], body, _) -> helpI body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
  and anf e =
    let ans, ans_setup = helpI e in
    List.fold_right
      (fun (bind, exp) body -> ELet ([(bind, exp, ())], body, ()))
      ans_setup ans
  in
  anf e
;;

(* NOTE: Assumes that e is in ANF *)
let rec count_vars (e : 'a expr) : int =
  match e with
  | EIf (_, t, f, _) -> max (count_vars t) (count_vars f)
  | ELet ([(_, b, _)], body, _) -> 1 + max (count_vars b) (count_vars body)
  | ENumber _ | EBool _ | EId _ | EPrim1 _ | EPrim2 _ -> 0
  | ELet _ -> raise (InternalCompilerError "Count vars called on non-ANF expr")
;;

let rec replicate (x : 'a) (i : int) : 'a list =
  match i with
  | 0 -> []
  | i when i > 0 -> x :: replicate x (i - 1)
  | _ ->
      raise
        (InternalCompilerError
           (sprintf "replicate called with negative value: %d" i) )
;;

let raise_if (b : bool) e : unit = if b then raise e else ()

let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) :
    instruction list =
  let bool_check_reg reg err_name =
    raise_if (reg == R11)
      (InternalCompilerError "cannot call bool_check_reg with R11");
    let err_label = sprintf "error_%s_not_boolean" err_name in
    [ IMov (Reg R11, Reg reg);
      (* Get relevant bits of boolean type tag *)
      IAnd (Reg R11, HexConst bool_tag_mask);
      (* Check whether they match the boolean type tag *)
      ICmp (Reg R11, HexConst bool_tag);
      (* Re-load from source reg after clobbering R11,*)
      IMov (Reg R11, Reg reg);
      (* If argument isn't a boolean, error *)
      IJne err_label ]
  in
  let num_check_reg reg err_name =
    let err_label = sprintf "error_%s_not_number" err_name in
    let first_move =
      match reg with
      | R11 -> ILineComment "Number to check is already in R11"
      | _ -> IMov (Reg R11, Reg reg)
    in
    [ first_move;
      (* Bitwise AND with the flag mask and observe the result *)
      ITest (Reg R11, HexConst num_tag_mask);
      (* Since num_tag is 0x0, error if result was non-zero *)
      IJnz err_label ]
  in
  match e with
  | ENumber _ | EBool _ | EId _ -> [IMov (Reg RAX, compile_imm e env)]
  | EPrim1 (((Add1 | Sub1) as op), n, _) ->
      let n_arg = compile_imm n env in
      let op_inst =
        match op with
        | Add1 -> IAdd (Reg RAX, Const 2L)
        | Sub1 -> ISub (Reg RAX, Const 2L)
        | _ -> raise (InternalCompilerError "invalid op in nested match")
      in
      [ ILineComment (sprintf "EPrim1 arith %s" (name_of_op1 op));
        (* Move in the argument *)
        IMov (Reg RAX, n_arg) ]
      @ num_check_reg RAX "arith"
      @ [ op_inst;
          (* After the operation was performed, check for overflow *)
          IJo "error_overflow" ]
  | EPrim1 (((IsBool | IsNum) as op), x, t) ->
      let done_label = sprintf "done_%d" t in
      let x_arg = compile_imm x env in
      let tag_mask, tag =
        match op with
        | IsBool -> (bool_tag_mask, bool_tag)
        | IsNum -> (num_tag_mask, num_tag)
        | _ -> raise (InternalCompilerError "invalid op in nested match")
      in
      [ ILineComment (sprintf "EPrim1 predicate %s" (name_of_op1 op));
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
        ILabel done_label ]
  | EPrim1 (Not, b, _) ->
      let n_arg = compile_imm b env in
      [ ILineComment (sprintf "EPrim1 logic %s" (name_of_op1 Not));
        (* Load the argument *)
        IMov (Reg RAX, n_arg) ]
      (* Value check the argument *)
      @ bool_check_reg RAX "logic"
      (* Flip the bit for bool *)
      @ [IBtc (Reg RAX, Const bool_bit)]
  | EPrim1 (Print, x, _) ->
      let x_arg = compile_imm x env in
      [ ILineComment "EPrim1 call Print";
        (* Set up argument *)
        IMov (Reg RDI, x_arg);
        (* Call method with no cleanup necessary after *)
        ICall "print" ]
  | EPrim1 (PrintStack, _, _) ->
      raise (NotYetImplemented "Unimplemented PrintStack for assignment 4")
  | EPrim2 (((And | Or) as op), lhs, rhs, t) ->
      let done_label = sprintf "done_%d" t in
      let lhs_arg = compile_imm lhs env in
      let rhs_insts = compile_expr rhs si env in
      let jmp_inst =
        match op with
        (* Jump when LHS is false so that AND results in false *)
        | And -> IJne done_label
        (* Jump when LHS is true so that OR results in true *)
        | Or -> IJe done_label
        | _ -> raise (InternalCompilerError "invalid op in nested match")
      in
      [ ILineComment (sprintf "EPrim2 logic %s" (name_of_op2 op));
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
      @ [ILabel done_label]
  | EPrim2 (((Plus | Minus | Times) as op), lhs, rhs, _) ->
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
      [ ILineComment (sprintf "EPrim2 arith %s" (name_of_op2 op));
        IMov (Reg RAX, lhs_arg) ]
      @ num_check_reg RAX "arith"
      (* Load rhs into R11 for checking *)
      @ [IMov (Reg R11, rhs_arg)]
      @ num_check_reg R11 "arith"
      (* Perform computation on RAX and R11 *)
      @ insts
      @ [ (* After the operation was performed, check for overflow *)
          IJo "error_overflow" ]
  | EPrim2 (Eq, lhs, rhs, tag) ->
      let done_label = sprintf "done_%d" tag in
      let lhs_arg = compile_imm lhs env in
      let rhs_arg = compile_imm rhs env in
      [ ILineComment (sprintf "EPrim2 comparison %s" (name_of_op2 Eq));
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
        ILabel done_label ]
  | EPrim2 (((Greater | GreaterEq | Less | LessEq) as op), lhs, rhs, tag) ->
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
      [ ILineComment (sprintf "EPrim2 comparison %s" (name_of_op2 op));
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
          ILabel done_label ]
  | EIf (cond, thn, els, tag) ->
      let else_label = sprintf "else_%d" tag in
      let done_label = sprintf "done_%d" tag in
      let c_arg = compile_imm cond env in
      let thn_comp = compile_expr thn si env in
      let els_comp = compile_expr els si env in
      [ ILineComment "EIf condition check";
        (* Load condition and check boolean-ness *)
        IMov (Reg RAX, c_arg) ]
      @ bool_check_reg RAX "if"
      (* Check if condition is true, if not jump to else *)
      @ [ ICmp (Reg RAX, HexConst const_true);
          IJne else_label;
          ILineComment "EIf then block" ]
      (* Evaluate then and and jump to done *)
      @ thn_comp
      @ [ IJmp done_label;
          (* Evaluate else branch and be done *)
          ILineComment "EIf else block";
          ILabel else_label ]
      @ els_comp @ [ILabel done_label]
  | ELet ([(id, e, _)], body, _) ->
      let let_name = sprintf "let$%s" id in
      let prelude = compile_expr e (si + 1) env in
      let body = compile_expr body (si + 1) ((id, si) :: env) in
      [ILineComment (sprintf "Let prelude %s" let_name)]
      (* Compute the binding value *)
      @ prelude
      @ [ ILineComment (sprintf "Let body %s" let_name);
          (* Move the binding on to stack *)
          IMov (RegOffset (~-si, RBP), Reg RAX) ]
      (* Excute the body in new context *)
      @ body
  | ELet _ -> raise (InternalCompilerError "Impossible: Not in ANF")

and compile_imm (e : tag expr) (env : (string * int) list) : arg =
  match e with
  | ENumber (n, _) ->
      if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L then
        raise
          (InternalCompilerError
             ("Number out of range in compile: " ^ Int64.to_string n) )
      else
        Const (Int64.mul n 2L)
  | EBool (true, _) -> HexConst const_true
  | EBool (false, _) -> HexConst const_false
  | EId (x, _) -> RegOffset (~-(find env x), RBP)
  | EPrim1 _ | EPrim2 _ | EIf _ | ELet _ ->
      raise (InternalCompilerError "Impossible: not an immediate")
;;

let compile_prog (anfed : tag expr) : string =
  (* Declare code section and runtime function names *)
  let prelude =
    "section .text\n\
     extern error\n\
     extern print\n\
     global our_code_starts_here\n\
     our_code_starts_here:"
  in
  (* Save the base register and reserve space on the stack *)
  let stack_setup =
    let num_vars = count_vars anfed in
    (* If even we increment num_vars to next odd number *)
    let aligned_vars = num_vars + Int.rem (num_vars + 1) 2 in
    [ IPush (Reg RBP);
      IMov (Reg RBP, Reg RSP);
      ISub (Reg RSP, Const (Int64.of_int (8 * aligned_vars))) ]
  in
  (* Decrement the stack pointer, restore the base, return *)
  let stack_teardown = [IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet] in
  (* Error routines that call non-returning error C function *)
  let error_routines =
    let error_routine (name : string) (code : int64) (reg : reg) =
      [ IInstrComment
          (ILabel (sprintf "error_%s" name), "never returning sub-routine");
        IMov (Reg RDI, HexConst code);
        IMov (Reg RSI, Reg reg);
        ICall "error";
        ILineComment "should never return" ]
    in
    (* Type errors come from testing arguments in the scratch register *)
    error_routine "logic_not_boolean" err_LOGIC_NOT_BOOL R11
    @ error_routine "if_not_boolean" err_IF_NOT_BOOL R11
    @ error_routine "arith_not_number" err_ARITH_NOT_NUM R11
    @ error_routine "comp_not_number" err_COMP_NOT_NUM R11
    (* Overflow errors come from the "answer in RAX" *)
    @ error_routine "overflow" err_OVERFLOW RAX
  in
  (* Compile user code for the body *)
  let body = compile_expr anfed 1 [] in
  (* Concatinate and print the instruction *)
  let as_assembly_string =
    let assembly_instrs =
      [ILineComment "stack setup"]
      @ stack_setup @ [ILineComment "body"] @ body
      @ [ILineComment "stack teardown"]
      @ stack_teardown
      @ [ILineComment "error handlers"]
      @ error_routines
    in
    to_asm assembly_instrs
  in
  sprintf "%s%s\n" prelude as_assembly_string
;;

let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed check_scope
  |> add_phase desugared desugar
  |> add_phase tagged tag |> add_phase renamed rename
  |> add_phase anfed (fun p -> tag (anf p))
  |> add_phase result compile_prog
;;
