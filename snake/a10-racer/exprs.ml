open Printf
open Utils

let show_debug_print = ref false

let debug_printf fmt =
  if !show_debug_print then printf fmt else ifprintf stdout fmt
;;

type tag = int

type sourcespan = Lexing.position * Lexing.position

type prim1 =
  | Add1
  | Sub1
  | IsBool
  | IsNum
  | IsTuple
  | Not
  | PrintStack

type eagerprim2 =
  | Plus
  | Minus
  | Times
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq

type lazyprim2 =
  | And
  | Or

type prim2 =
  | EP2 of eagerprim2
  | LP2 of lazyprim2

and 'a bind =
  | BBlank of 'a
  | BName of string * bool * 'a
  | BTuple of 'a bind list * 'a

and 'a binding = 'a bind * 'a expr * 'a

and 'a expr =
  | ENumber of int64 * 'a
  | EBool of bool * 'a
  | EId of string * 'a
  | ENil of 'a
  | ETuple of 'a expr list * 'a
  | EGetItem of 'a expr * 'a expr * 'a
  | ESetItem of 'a expr * 'a expr * 'a expr * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | ELambda of 'a bind list * 'a expr * 'a
  | ENativeApp of string * 'a expr list * 'a
  | EApp of 'a expr * 'a expr list * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ESeq of 'a expr * 'a expr * 'a
  | ELet of 'a binding list * 'a expr * 'a
  | ELetRec of 'a binding list * 'a expr * 'a

type 'a decl = DFun of string * 'a bind list * 'a expr * 'a

type 'a program = Program of 'a decl list list * 'a expr * 'a

type 'a immexpr =
  (* immediate expressions *)
  | ImmNum of int64 * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a
  | ImmNil of 'a

and 'a cexpr =
  (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CEPrim2 of eagerprim2 * 'a immexpr * 'a immexpr * 'a
  | CLPrim2 of lazyprim2 * 'a immexpr * 'a aexpr * 'a
  | CNativeApp of string * 'a immexpr list * 'a
  | CApp of 'a immexpr * 'a immexpr list * 'a
  | CImmExpr of 'a immexpr (* for when you just need an immediate value *)
  | CTuple of 'a immexpr list * 'a
  | CGetItem of 'a immexpr * 'a immexpr * 'a
  | CSetItem of 'a immexpr * 'a immexpr * 'a immexpr * 'a
  | CLambda of string list * 'a aexpr * string list * 'a

and 'a aexpr =
  (* anf expressions *)
  | ASeq of 'a cexpr * 'a aexpr * 'a
  | ALet of string * 'a cexpr * 'a aexpr * 'a
  | ALetRec of (string * 'a cexpr) list * 'a aexpr * 'a
  | ACExpr of 'a cexpr

and 'a aprogram = AProgram of 'a aexpr * 'a

type alloc_strategy =
  | Register
  | Naive

let string_of_alloc_strategy strat =
  match strat with
  | Register -> "register"
  | Naive -> "naive"
;;

let bind_of_binding ((b, _, _) : 'a binding) : 'a bind = b

(* Extracts the names and there info from a binding. Blanks are skipped *)
let rec names_infos_of_bind (b : 'a bind) : (string * 'a) list =
  match b with
  | BBlank _ -> []
  | BName (n, _, a) -> [(n, a)]
  | BTuple (binds, _) -> flat_map names_infos_of_bind binds
;;

let info_of_decl (DFun (_, _, _, a) : 'a decl) : 'a = a

let name_of_decl (DFun (name, _, _, _) : 'a decl) : string = name

let name_info_of_decl (DFun (name, _, _, info) : 'a decl) : string * 'a =
  (name, info)
;;

let decl_name_matches (name : string) (DFun (dn, _, _, _) : 'a decl) : bool =
  dn = name
;;

let map_opt f v =
  match v with
  | None -> None
  | Some v -> Some (f v)
;;

let get_tag_E e =
  match e with
  | ELet (_, _, t)
   |ELetRec (_, _, t)
   |EPrim1 (_, _, t)
   |EPrim2 (_, _, _, t)
   |EIf (_, _, _, t)
   |ENil t
   |ENumber (_, t)
   |EBool (_, t)
   |EId (_, t)
   |ENativeApp (_, _, t)
   |EApp (_, _, t)
   |ETuple (_, t)
   |EGetItem (_, _, t)
   |ESetItem (_, _, _, t)
   |ESeq (_, _, t)
   |ELambda (_, _, t) -> t
;;

let get_tag_D d =
  match d with
  | DFun (_, _, _, t) -> t
;;

let rec map_tag_E (f : 'a -> 'b) (e : 'a expr) =
  match e with
  | ESeq (e1, e2, a) -> ESeq (map_tag_E f e1, map_tag_E f e2, f a)
  | ETuple (exprs, a) -> ETuple (List.map (map_tag_E f) exprs, f a)
  | EGetItem (e, idx, a) -> EGetItem (map_tag_E f e, map_tag_E f idx, f a)
  | ESetItem (e, idx, newval, a) ->
      ESetItem (map_tag_E f e, map_tag_E f idx, map_tag_E f newval, f a)
  | EId (x, a) -> EId (x, f a)
  | ENumber (n, a) -> ENumber (n, f a)
  | EBool (b, a) -> EBool (b, f a)
  | ENil a -> ENil (f a)
  | EPrim1 (op, e, a) ->
      let tag_prim = f a in
      EPrim1 (op, map_tag_E f e, tag_prim)
  | EPrim2 (op, e1, e2, a) ->
      let tag_prim = f a in
      let tag_e1 = map_tag_E f e1 in
      let tag_e2 = map_tag_E f e2 in
      EPrim2 (op, tag_e1, tag_e2, tag_prim)
  | ELet (binds, body, a) ->
      let tag_let = f a in
      let tag_binding (b, e, t) =
        let tag_bind = f t in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELet (tag_binds, tag_body, tag_let)
  | ELetRec (binds, body, a) ->
      let tag_let = f a in
      let tag_binding (b, e, t) =
        let tag_bind = f t in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELetRec (tag_binds, tag_body, tag_let)
  | EIf (cond, thn, els, a) ->
      let tag_if = f a in
      let tag_cond = map_tag_E f cond in
      let tag_thn = map_tag_E f thn in
      let tag_els = map_tag_E f els in
      EIf (tag_cond, tag_thn, tag_els, tag_if)
  | ENativeApp (fname, args, a) ->
      let tag_app = f a in
      ENativeApp (fname, List.map (map_tag_E f) args, tag_app)
  | EApp (func, args, a) ->
      let tag_app = f a in
      EApp (map_tag_E f func, List.map (map_tag_E f) args, tag_app)
  | ELambda (binds, body, a) ->
      let tag_lam = f a in
      ELambda (List.map (map_tag_B f) binds, map_tag_E f body, tag_lam)

and map_tag_B (f : 'a -> 'b) b =
  match b with
  | BBlank tag -> BBlank (f tag)
  | BName (x, allow_shadow, ax) ->
      let tag_ax = f ax in
      BName (x, allow_shadow, tag_ax)
  | BTuple (binds, t) ->
      let tag_tup = f t in
      BTuple (List.map (map_tag_B f) binds, tag_tup)

and map_tag_D (f : 'a -> 'b) d =
  match d with
  | DFun (name, args, body, a) ->
      let tag_fun = f a in
      let tag_args = List.map (map_tag_B f) args in
      let tag_body = map_tag_E f body in
      DFun (name, tag_args, tag_body, tag_fun)

and map_tag_P (f : 'a -> 'b) p =
  match p with
  | Program (declgroups, body, a) ->
      let tag_a = f a in
      let tag_decls =
        List.map (fun group -> List.map (map_tag_D f) group) declgroups
      in
      let tag_body = map_tag_E f body in
      Program (tag_decls, tag_body, tag_a)
;;

let tag (p : 'a program) : tag program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next
  in
  map_tag_P tag p
;;

let combine_tags (f1 : 'a -> 'b) (f2 : 'a -> 'c) (p : 'a program) :
    ('b * 'c) program =
  map_tag_P (fun a -> (f1 a, f2 a)) p
;;

let tag_and_map (f : 'a -> 'b) (p : 'a program) : ('a * 'b) program =
  map_tag_P (fun a -> (a, f a)) p
;;

let prog_and_tag (p : 'a program) : ('a * tag) program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next
  in
  tag_and_map tag p
;;

let rec untagP (p : 'a program) : unit program =
  match p with
  | Program (decls, body, _) ->
      Program
        (List.map (fun group -> List.map untagD group) decls, untagE body, ())

and untagE e =
  match e with
  | ESeq (e1, e2, _) -> ESeq (untagE e1, untagE e2, ())
  | ETuple (exprs, _) -> ETuple (List.map untagE exprs, ())
  | EGetItem (e, idx, _) -> EGetItem (untagE e, untagE idx, ())
  | ESetItem (e, idx, newval, _) ->
      ESetItem (untagE e, untagE idx, untagE newval, ())
  | EId (x, _) -> EId (x, ())
  | ENumber (n, _) -> ENumber (n, ())
  | EBool (b, _) -> EBool (b, ())
  | ENil _ -> ENil ()
  | EPrim1 (op, e, _) -> EPrim1 (op, untagE e, ())
  | EPrim2 (op, e1, e2, _) -> EPrim2 (op, untagE e1, untagE e2, ())
  | ELet (binds, body, _) ->
      ELet
        ( List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds,
          untagE body,
          () )
  | EIf (cond, thn, els, _) -> EIf (untagE cond, untagE thn, untagE els, ())
  | ENativeApp (fname, args, _) -> ENativeApp (fname, List.map untagE args, ())
  | EApp (func, args, _) -> EApp (untagE func, List.map untagE args, ())
  | ELetRec (binds, body, _) ->
      ELetRec
        ( List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds,
          untagE body,
          () )
  | ELambda (binds, body, _) -> ELambda (List.map untagB binds, untagE body, ())

and untagB b =
  match b with
  | BBlank _ -> BBlank ()
  | BName (x, allow_shadow, _) -> BName (x, allow_shadow, ())
  | BTuple (binds, _) -> BTuple (List.map untagB binds, ())

and untagD d =
  match d with
  | DFun (name, args, body, _) ->
      DFun (name, List.map untagB args, untagE body, ())
;;

let rec get_tag_A (e : 'a aexpr) : 'a =
  match e with
  | ASeq (_, _, a) -> a
  | ALet (_, _, _, a) -> a
  | ALetRec (_, _, a) -> a
  | ACExpr c -> get_tag_C c

and get_tag_C (c : 'a cexpr) : 'a =
  match c with
  | CPrim1 (_, _, a) -> a
  | CEPrim2 (_, _, _, a) -> a
  | CLPrim2 (_, _, _, a) -> a
  | CIf (_, _, _, a) -> a
  | CNativeApp (_, _, a) -> a
  | CApp (_, _, a) -> a
  | CImmExpr i -> get_tag_I i
  | CTuple (_, a) -> a
  | CGetItem (_, _, a) -> a
  | CSetItem (_, _, _, a) -> a
  | CLambda (_, _, _, a) -> a

and get_tag_I (i : 'a immexpr) : 'a =
  match i with
  | ImmNil a -> a
  | ImmId (_, a) -> a
  | ImmNum (_, a) -> a
  | ImmBool (_, a) -> a
;;

let map_tag_A (f : 'a -> 'b) (p : 'a aprogram) : 'b aprogram =
  let helpI (i : 'a immexpr) : 'b immexpr =
    match i with
    | ImmNil a -> ImmNil (f a)
    | ImmId (x, a) -> ImmId (x, f a)
    | ImmNum (n, a) -> ImmNum (n, f a)
    | ImmBool (b, a) -> ImmBool (b, f a)
  in
  let rec helpA (e : 'a aexpr) : 'b aexpr =
    match e with
    | ASeq (e1, e2, a) -> ASeq (helpC e1, helpA e2, f a)
    | ALet (x, c, b, a) -> ALet (x, helpC c, helpA b, f a)
    | ALetRec (xcs, b, a) ->
        ALetRec (List.map (fun (x, c) -> (x, helpC c)) xcs, helpA b, f a)
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : 'a cexpr) : 'b cexpr =
    match c with
    | CPrim1 (op, e, a) -> CPrim1 (op, helpI e, f a)
    | CEPrim2 (op, e1, e2, a) -> CEPrim2 (op, helpI e1, helpI e2, f a)
    | CLPrim2 (op, e1, e2, a) -> CLPrim2 (op, helpI e1, helpA e2, f a)
    | CIf (cond, thn, els, a) -> CIf (helpI cond, helpA thn, helpA els, f a)
    | CNativeApp (fname, args, a) -> CNativeApp (fname, List.map helpI args, f a)
    | CApp (func, args, a) -> CApp (helpI func, List.map helpI args, f a)
    | CImmExpr i -> CImmExpr (helpI i)
    | CTuple (es, a) -> CTuple (List.map helpI es, f a)
    | CGetItem (e, idx, a) -> CGetItem (helpI e, helpI idx, f a)
    | CSetItem (e, idx, newval, a) ->
        CSetItem (helpI e, helpI idx, helpI newval, f a)
    | CLambda (args, body, free_vars, a) ->
        CLambda (args, helpA body, free_vars, f a)
  in
  let helpP (p : 'a aprogram) : 'b aprogram =
    match p with
    | AProgram (body, a) -> AProgram (helpA body, f a)
  in
  helpP p
;;

let atag (p : 'a aprogram) : tag aprogram =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next
  in
  map_tag_A tag p
;;

let auntag (p : 'a aprogram) : unit aprogram = map_tag_A (Fun.const ()) p

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq (e1, e2, _) -> max (helpC e1) (helpA e2)
    | ALet (_, bind, body, _) -> 1 + max (helpC bind) (helpA body)
    | ALetRec (binds, body, _) ->
        List.length binds
        + List.fold_left max (helpA body)
            (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (_, t, f, _) -> max (helpA t) (helpA f)
    | CLPrim2 (_, _, rhs, _) -> helpA rhs
    | CEPrim2 _
     |CPrim1 _
     |CImmExpr _
     |CLambda _
     |CApp _
     |CNativeApp _
     |CTuple _
     |CGetItem _
     |CSetItem _ -> 0
  in
  helpA e
;;

let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program (decls, body, tag) ->
        Program
          ( List.map (fun group -> List.map (helpD env) group) decls,
            helpE env body,
            tag )
  and helpD env decl =
    match decl with
    | DFun (name, args, body, tag) ->
        let newArgs, env' = helpBS env args in
        DFun (name, newArgs, helpE env' body, tag)
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
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE env e in
        let bindings', env'' = helpBG env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE env e1, helpE env e2, tag)
    | ETuple (es, tag) -> ETuple (List.map (helpE env) es, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE env e, helpE env idx, tag)
    | ESetItem (e, idx, newval, tag) ->
        ESetItem (helpE env e, helpE env idx, helpE env newval, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE env arg, tag)
    | EPrim2 (op, left, right, tag) ->
        EPrim2 (op, helpE env left, helpE env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId (name, tag) -> EId (List.assoc name env, tag)
    | ENativeApp (fname, args, tag) ->
        ENativeApp (fname, List.map (helpE env) args, tag)
    | EApp (func, args, tag) ->
        let func = helpE env func in
        EApp (func, List.map (helpE env) args, tag)
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG env binds in
        let body' = helpE env' body in
        ELet (binds', body', tag)
    | ELetRec (bindings, body, tag) ->
        let revbinds, env =
          List.fold_left
            (fun (revbinds, env) (b, e, t) ->
              let b, env = helpB env b in
              ((b, e, t) :: revbinds, env) )
            ([], env) bindings
        in
        let bindings' =
          List.fold_left
            (fun bindings (b, e, tag) -> (b, helpE env e, tag) :: bindings)
            [] revbinds
        in
        let body' = helpE env body in
        ELetRec (bindings', body', tag)
    | ELambda (binds, body, tag) ->
        let binds', env' = helpBS env binds in
        let body' = helpE env' body in
        ELambda (binds', body', tag)
  in
  rename [] p
;;
