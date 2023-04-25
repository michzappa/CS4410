open Printf

let show_debug_print = ref false

let debug_printf fmt =
  if !show_debug_print then
    printf fmt
  else
    ifprintf stdout fmt
;;

type sourcespan = Lexing.position * Lexing.position

type tag = int

type prim1 =
  | Add1
  | Sub1
  | Print
  | IsBool
  | IsNum
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

type 'a bind = string * 'a expr * 'a

and 'a expr =
  | ENumber of int64 * 'a
  | EBool of bool * 'a
  | EId of string * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | EApp of string * 'a expr list * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ELet of 'a bind list * 'a expr * 'a

type 'a decl = DFun of string * (string * 'a) list * 'a expr * 'a

type 'a program = Program of 'a decl list * 'a expr * 'a

type 'a immexpr =
  (* immediate expressions *)
  | ImmNum of int64 * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a

type 'a cexpr =
  (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CEPrim2 of eagerprim2 * 'a immexpr * 'a immexpr * 'a
  | CLPrim2 of lazyprim2 * 'a immexpr * 'a aexpr * 'a
  | CApp of string * 'a immexpr list * 'a
  | CImmExpr of 'a immexpr (* for when you just need an immediate value *)

and 'a aexpr =
  (* anf expressions *)
  | ALet of string * 'a cexpr * 'a aexpr * 'a
  | ACExpr of 'a cexpr

and 'a adecl = ADFun of string * string list * 'a aexpr * 'a

and 'a aprogram = AProgram of 'a adecl list * 'a aexpr * 'a

let info_of_bind ((_, _, a) : 'a bind) : 'a = a

let name_of_bind ((name, _, _) : 'a bind) : string = name

let bind_name_matches (name : string) ((bn, _, _) : 'a bind) : bool = bn = name

let info_of_decl (DFun (_, _, _, a) : 'a decl) : 'a = a

let name_of_decl (DFun (name, _, _, _) : 'a decl) : string = name

let decl_name_matches (name : string) (DFun (dn, _, _, _) : 'a decl) : bool =
  dn = name
;;

let name_of_adecl (ADFun (name, _, _, _) : 'a adecl) : string = name

let tag (p : 'a program) : tag program =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next
  in
  let rec helpE (e : 'a expr) : tag expr =
    match e with
    | EId (x, _) -> EId (x, tag ())
    | ENumber (n, _) -> ENumber (n, tag ())
    | EBool (b, _) -> EBool (b, tag ())
    | EPrim1 (op, e, _) ->
        let prim_tag = tag () in
        EPrim1 (op, helpE e, prim_tag)
    | EPrim2 (op, e1, e2, _) ->
        let prim_tag = tag () in
        EPrim2 (op, helpE e1, helpE e2, prim_tag)
    | ELet (binds, body, _) ->
        let let_tag = tag () in
        ELet
          ( List.map
              (fun (x, b, _) ->
                let t = tag () in
                (x, helpE b, t) )
              binds,
            helpE body,
            let_tag )
    | EIf (cond, thn, els, _) ->
        let if_tag = tag () in
        EIf (helpE cond, helpE thn, helpE els, if_tag)
    | EApp (name, args, _) ->
        let app_tag = tag () in
        EApp (name, List.map helpE args, app_tag)
  and helpD d =
    match d with
    | DFun (name, args, body, _) ->
        let fun_tag = tag () in
        DFun
          (name, List.map (fun (a, _) -> (a, tag ())) args, helpE body, fun_tag)
  and helpP p =
    match p with
    | Program (decls, body, _) -> Program (List.map helpD decls, helpE body, 0)
  in
  helpP p
;;

let untag (p : 'a program) : unit program =
  let rec helpB (x, b, _) = (x, helpE b, ())
  and helpE e =
    match e with
    | EId (x, _) -> EId (x, ())
    | ENumber (n, _) -> ENumber (n, ())
    | EBool (b, _) -> EBool (b, ())
    | EPrim1 (op, e, _) -> EPrim1 (op, helpE e, ())
    | EPrim2 (op, e1, e2, _) -> EPrim2 (op, helpE e1, helpE e2, ())
    | ELet (binds, body, _) -> ELet (List.map helpB binds, helpE body, ())
    | EIf (cond, thn, els, _) -> EIf (helpE cond, helpE thn, helpE els, ())
    | EApp (name, args, _) -> EApp (name, List.map helpE args, ())
  and helpD d =
    match d with
    | DFun (name, args, body, _) ->
        DFun (name, List.map (fun (a, _) -> (a, ())) args, helpE body, ())
  and helpP p =
    match p with
    | Program (decls, body, _) -> Program (List.map helpD decls, helpE body, ())
  in
  helpP p
;;

let atag (p : 'a aprogram) : tag aprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next
  in
  let rec helpA (e : 'a aexpr) : tag aexpr =
    match e with
    | ALet (x, c, b, _) ->
        let let_tag = tag () in
        ALet (x, helpC c, helpA b, let_tag)
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : 'a cexpr) : tag cexpr =
    match c with
    | CPrim1 (op, e, _) ->
        let prim_tag = tag () in
        CPrim1 (op, helpI e, prim_tag)
    | CEPrim2 (op, e1, e2, _) ->
        let prim_tag = tag () in
        CEPrim2 (op, helpI e1, helpI e2, prim_tag)
    | CLPrim2 (op, e1, e2, _) ->
        let prim_tag = tag () in
        CLPrim2 (op, helpI e1, helpA e2, prim_tag)
    | CIf (cond, thn, els, _) ->
        let if_tag = tag () in
        CIf (helpI cond, helpA thn, helpA els, if_tag)
    | CApp (name, args, _) ->
        let app_tag = tag () in
        CApp (name, List.map helpI args, app_tag)
    | CImmExpr i -> CImmExpr (helpI i)
  and helpI (i : 'a immexpr) : tag immexpr =
    match i with
    | ImmId (x, _) -> ImmId (x, tag ())
    | ImmNum (n, _) -> ImmNum (n, tag ())
    | ImmBool (b, _) -> ImmBool (b, tag ())
  and helpD d =
    match d with
    | ADFun (name, args, body, _) ->
        let fun_tag = tag () in
        ADFun (name, args, helpA body, fun_tag)
  and helpP p =
    match p with
    | AProgram (decls, body, _) -> AProgram (List.map helpD decls, helpA body, 0)
  in
  helpP p
;;
