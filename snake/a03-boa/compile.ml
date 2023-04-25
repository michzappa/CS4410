open Printf
open Exprs
open Pretty

let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

let info_of_expr (e : 'a expr) : 'a =
  match e with
  | ENumber (_, info)
   |EId (_, info)
   |EPrim1 (_, _, info)
   |EPrim2 (_, _, _, info)
   |EIf (_, _, _, info)
   |ELet (_, _, info) -> info
;;

let is_imm e =
  match e with
  | ENumber _ | EId _ -> true
  | EPrim1 _ | EPrim2 _ | ELet _ | EIf _ -> false
;;

let rec is_anf (e : 'a expr) : bool =
  match e with
  | ENumber _ | EId _ -> true
  | EPrim1 (_, e, _) -> is_imm e
  | EPrim2 (_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet (binds, body, _) ->
      List.for_all (fun (_, e, _) -> is_anf e) binds && is_anf body
  | EIf (cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
;;

(* PROBLEM 1 *)
(* This function should encapsulate the binding-error checking from Boa *)
exception BindingError of string

let check_scope (e : (Lexing.position * Lexing.position) expr) : unit =
  let rec check_scope_help
      (exp : (Lexing.position * Lexing.position) expr)
      (env : string list) : unit =
    match exp with
    | EId (s, _) when List.mem s env -> ()
    | EId (s, loc) ->
        raise
          (BindingError
             (sprintf "Unbound identifier '%s' at %s" s (string_of_pos loc)) )
    | EPrim1 (_, body, _) -> check_scope_help body env
    | EPrim2 (_, l, r, _) -> check_scope_help l env; check_scope_help r env
    | EIf (c, t, f, _) ->
        check_scope_help c env; check_scope_help t env; check_scope_help f env
    | ENumber (_, _) -> ()
    | ELet (bindings, body, _) ->
        let new_env = check_bindings_help bindings env [] in
        check_scope_help body new_env
  and check_bindings_help
      (bindings : (Lexing.position * Lexing.position) bind list)
      (env_acc : string list)
      (names_in_let : string list) : string list =
    match bindings with
    | [] -> env_acc
    | (name, _, loc) :: _ when List.mem name names_in_let ->
        raise
          (BindingError
             (sprintf "Repeat name '%s' in binding at %s" name
                (string_of_pos loc) ) )
    | (name, bind, _) :: rest ->
        check_scope_help bind env_acc;
        check_bindings_help rest (name :: env_acc) (name :: names_in_let)
  in
  check_scope_help e []
;;

type tag = int

(* PROBLEM 2 *)
(* This function assigns a unique tag to every subexpression and let binding *)
let tag (e : 'a expr) : tag expr =
  let rec tag_help (exp : 'a expr) (next_tag : int) : tag expr * int =
    match exp with
    | EId (name, _) -> (EId (name, next_tag), next_tag + 1)
    | ENumber (n, _) -> (ENumber (n, next_tag), next_tag + 1)
    | EPrim1 (op, e, _) ->
        let e, next_tag = tag_help e next_tag in
        (EPrim1 (op, e, next_tag), next_tag + 1)
    | EPrim2 (op, l, r, _) ->
        let l, next_tag = tag_help l next_tag in
        let r, next_tag = tag_help r next_tag in
        (EPrim2 (op, l, r, next_tag), next_tag + 1)
    | ELet (binds, body, _) ->
        let tag_bind (acc, next_tag) (name, bind, _) : tag bind list * tag =
          let bind, next_tag = tag_help bind next_tag in
          ((name, bind, next_tag) :: acc, next_tag + 1)
        in
        let binds, next_tag = List.fold_left tag_bind ([], next_tag) binds in
        let body, next_tag = tag_help body next_tag in
        let binds = List.rev binds in
        (ELet (binds, body, next_tag), next_tag + 1)
    | EIf (c, t, f, _) ->
        let c, next_tag = tag_help c next_tag in
        let t, next_tag = tag_help t next_tag in
        let f, next_tag = tag_help f next_tag in
        (EIf (c, t, f, next_tag), next_tag + 1)
  in
  let e, _ = tag_help e 1 in
  e
;;

(* This function removes all tags, and replaces them with the unit value.
   This might be convenient for testing, when you don't care about the tag info. *)
let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId (x, _) -> EId (x, ())
  | ENumber (n, _) -> ENumber (n, ())
  | EPrim1 (op, e, _) -> EPrim1 (op, untag e, ())
  | EPrim2 (op, e1, e2, _) -> EPrim2 (op, untag e1, untag e2, ())
  | ELet (binds, body, _) ->
      ELet (List.map (fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf (cond, thn, els, _) -> EIf (untag cond, untag thn, untag els, ())
;;

(* PROBLEM 3 *)
let rename (e : tag expr) : tag expr =
  let rec rename_help (env : (string * string) list) (e : tag expr) =
    let rename_env = rename_help env in
    match e with
    | ENumber (_, _) -> e
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

(* PROBLEM 4 & 5 *)
(* This function converts a tagged expression into an untagged expression in A-normal form *)
let rec anf_4410 (e : tag expr) : unit expr =
  let rec anf_help (e : tag expr) : unit expr * (string * unit expr) list =
    match e with
    | EId _ | ENumber _ -> (untag e, [])
    | EPrim1 (op, body, tag) ->
        let body_ans, body_ctx = anf_help body in
        let imm_name = sprintf "$prim1_%d" tag in
        let ans = EId (imm_name, ()) in
        let ctx = body_ctx @ [(imm_name, EPrim1 (op, body_ans, ()))] in
        (ans, ctx)
    | EPrim2 (op, l, r, tag) ->
        let l_ans, l_ctx = anf_help l in
        let r_ans, r_ctx = anf_help r in
        let imm_name = sprintf "$prim2_%d" tag in
        let ans = EId (imm_name, ()) in
        let ctx = l_ctx @ r_ctx @ [(imm_name, EPrim2 (op, l_ans, r_ans, ()))] in
        (ans, ctx)
    | EIf (c, t, f, tag) ->
        let c_ans, c_ctx = anf_help c in
        let imm_name = sprintf "$if_%d" tag in
        let ans = EIf (c_ans, anf_4410 t, anf_4410 f, ()) in
        let ctx = c_ctx @ [(imm_name, ans)] in
        (EId (imm_name, ()), ctx)
    | ELet (binds, body, tag) ->
        let anf_bind (name, bind, _) : (string * unit expr) list =
          let bind_ans, bind_ctx = anf_help bind in
          bind_ctx @ [(name, bind_ans)]
        in
        let binds_ctx = binds |> List.map anf_bind |> List.flatten in
        let body_ans, body_ctx = anf_help body in
        let temp = sprintf "$let_%d" tag in
        let ans = EId (temp, ()) in
        let ctx = binds_ctx @ body_ctx @ [(temp, body_ans)] in
        (ans, ctx)
  in
  let body, binds = anf_help e in
  List.fold_right
    (fun (name, bind) body -> ELet ([(name, bind, ())], body, ()))
    binds body
;;

(* Attempt at the 6410 challenge *)
let anf (e : tag expr) : unit expr =
  (* Create a separate let for each binding *)
  let letify (body, binds) =
    List.fold_right
      (fun (name, bind) body -> ELet ([(name, bind, ())], body, ()))
      binds body
  in
  let rec helpC (e : tag expr) : unit expr =
    match e with
    | EId _ | ENumber _ -> untag e
    | EPrim1 (op, body, _) ->
        let body_ans, body_ctx = helpI body in
        letify (EPrim1 (op, body_ans, ()), body_ctx)
    | EPrim2 (op, l, r, _) ->
        let l_ans, l_ctx = helpI l in
        let r_ans, r_ctx = helpI r in
        letify (EPrim2 (op, l_ans, r_ans, ()), l_ctx @ r_ctx)
    | EIf (cond, thn, els, _) ->
        let c_ans, c_ctx = helpI cond in
        letify (EIf (c_ans, helpC thn, helpC els, ()), c_ctx)
    | ELet (binds, body, _) ->
        let rec process (name, bind, _) body =
          ELet ([(name, helpC bind, ())], body, ())
        in
        List.fold_right process binds (helpC body)
  and helpI (e : tag expr) : unit expr * (string * unit expr) list =
    match e with
    | EId _ | ENumber _ -> (untag e, [])
    | EPrim1 (op, body, tag) ->
        let body_ans, body_ctx = helpI body in
        let imm_name = sprintf "$prim1_%d" tag in
        let ans = EId (imm_name, ()) in
        let ctx = body_ctx @ [(imm_name, EPrim1 (op, body_ans, ()))] in
        (ans, ctx)
    | EPrim2 (op, l, r, tag) ->
        let l_ans, l_ctx = helpI l in
        let r_ans, r_ctx = helpI r in
        let imm_name = sprintf "$prim2_%d" tag in
        let ans = EId (imm_name, ()) in
        let ctx = l_ctx @ r_ctx @ [(imm_name, EPrim2 (op, l_ans, r_ans, ()))] in
        (ans, ctx)
    | EIf (c, t, f, tag) ->
        let c_ans, c_ctx = helpI c in
        let imm_name = sprintf "$if_%d" tag in
        let ans = EIf (c_ans, helpC t, helpC f, ()) in
        let ctx = c_ctx @ [(imm_name, ans)] in
        (EId (imm_name, ()), ctx)
    | ELet (_, _, tag) ->
        let ans = helpC e in
        let imm_name = sprintf "$let_%d" tag in
        let ctx = [(imm_name, ans)] in
        let ans = EId (imm_name, ()) in
        (ans, ctx)
  in
  let anfed = helpC e in
  if not (is_anf anfed) then
    failwith
      (sprintf "ICE - ANF did not produce an ANF: %s" (string_of_expr anfed))
  else
    anfed
;;

(* Helper functions *)
let r_to_asm (r : reg) : string =
  match r with
  | RAX -> "rax"
  | RSP -> "rsp"
;;

let arg_to_asm (a : arg) : string =
  match a with
  | Const n -> sprintf "QWORD %Ld" n
  | Reg r -> r_to_asm r
  | RegOffset (n, r) ->
      if n >= 0 then
        sprintf "[%s+%d]" (r_to_asm r) (word_size * n)
      else
        sprintf "[%s-%d]" (r_to_asm r) (-1 * word_size * n)
;;

let i_to_asm (i : instruction) : string =
  match i with
  | IMov (dest, value) ->
      sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd (dest, to_add) ->
      sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | ISub (dest, to_sub) ->
      sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm to_sub)
  | IMul (dest, to_mul) ->
      sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm to_mul)
  | ILabel name -> sprintf "%s:" name
  | ICmp (lhs, rhs) -> sprintf "  cmp %s, %s" (arg_to_asm lhs) (arg_to_asm rhs)
  | IJne name -> sprintf "  jne %s" name
  | IJe name -> sprintf "  je %s" name
  | IJmp name -> sprintf "  jmp %s" name
  | IRet -> "  ret"
;;

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is
;;

(* PROBLEM 5 *)
(* This function actually compiles the tagged ANF expression into assembly *)
(* The si parameter should be used to indicate the next available stack index for use by Lets *)
(* The env parameter associates identifier names to stack indices *)
let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) :
    instruction list =
  match e with
  | ENumber (_, _) | EId (_, _) -> [IMov (Reg RAX, compile_imm e env)]
  | EPrim1 (op, e, _) ->
      let e_arg = compile_imm e env in
      let inst =
        match op with
        | Add1 -> IAdd (Reg RAX, Const 1L)
        | Sub1 -> ISub (Reg RAX, Const 1L)
      in
      [IMov (Reg RAX, e_arg); inst]
  | EPrim2 (op, left, right, _) ->
      let l_arg = compile_imm left env in
      let r_arg = compile_imm right env in
      let inst =
        match op with
        | Plus -> IAdd (Reg RAX, r_arg)
        | Minus -> ISub (Reg RAX, r_arg)
        | Times -> IMul (Reg RAX, r_arg)
      in
      [IMov (Reg RAX, l_arg); inst]
  | EIf (cond, thn, els, tag) ->
      let else_label = sprintf "else_%d" tag in
      let done_label = sprintf "done_%d" tag in
      let c_arg = compile_imm cond env in
      let thn_comp = compile_expr thn si env in
      let els_comp = compile_expr els si env in
      [IMov (Reg RAX, c_arg); ICmp (Reg RAX, Const 0L); IJe else_label]
      @ thn_comp
      @ [IJmp done_label; ILabel else_label]
      @ els_comp @ [ILabel done_label]
  | ELet ([(name, bind, _)], body, _) ->
      let bind_comp = compile_expr bind si env in
      let body_comp = compile_expr body (si + 1) ((name, si) :: env) in
      bind_comp @ [IMov (RegOffset (-1 * si, RSP), Reg RAX)] @ body_comp
  | _ -> failwith "Impossible: Not in ANF"

and compile_imm e env =
  match e with
  | ENumber (n, _) -> Const n
  | EId (x, _) -> RegOffset (~-(find env x), RSP)
  | _ -> failwith "Impossible: not an immediate"
;;

let compile_anf_to_string anfed =
  let prelude =
    "section .text\nglobal our_code_starts_here\nour_code_starts_here:"
  in
  let compiled = compile_expr anfed 1 [] in
  let as_assembly_string = to_asm (compiled @ [IRet]) in
  sprintf "%s%s\n" prelude as_assembly_string
;;

let compile_to_string prog =
  check_scope prog;
  let tagged : tag expr = tag prog in
  let renamed : tag expr = rename tagged in
  let anfed : tag expr = tag (anf renamed) in
  (* printf "Prog:\n%s\n" (ast_of_expr prog); *)
  (* printf "Tagged:\n%s\n" (format_expr tagged string_of_int); *)
  (* printf "ANFed/tagged:\n%s\n" (format_expr anfed string_of_int); *)
  compile_anf_to_string anfed
;;
