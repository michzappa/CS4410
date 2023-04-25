open Graph
open Exprs
open Environment
open Phases
open Assembly
open Utils

let interfere (e : ('a * freevarst) aexpr) (live : StringSet.t) : grapht =
  let rec helpA
      (aexp : ('a * freevarst) aexpr)
      (live_across : StringSet.t)
      (surrounding : grapht) : grapht =
    match aexp with
    | ALet (name, bind, body, _) ->
        let graph = helpA body live_across surrounding in
        let _, fvs_body = get_tag_A body in
        let live_vars =
          StringSet.diff
            (StringSet.union fvs_body live_across)
            (StringSet.singleton name)
        in
        let graph = add_node graph name in
        let graph =
          StringSet.fold (fun fv acc -> add_edge acc fv name) live_vars graph
        in
        helpC bind live_vars graph
    | ACExpr cexpr -> helpC cexpr live_across surrounding
    | ASeq (lhs, rhs, _) ->
        let graph = helpA rhs live_across surrounding in
        let _, fvs_body = get_tag_A rhs in
        let live_vars = StringSet.union fvs_body live_across in
        helpC lhs live_vars graph
    | ALetRec (bindings, body, _) ->
        let graph = helpA body live_across surrounding in
        (* Interfere every bound lambda name with every free variable in the bound lambdas *)
        let bound_names, bound_lambdas = List.split bindings in
        let interfering_names =
          StringSet.union
            (StringSet.of_list bound_names)
            (List.fold_right
               (fun cexp acc -> StringSet.union acc (snd (get_tag_C cexp)))
               bound_lambdas StringSet.empty )
        in
        let graph = graph_from_nodes ~init_graph:graph interfering_names in
        (* Interfere every fv in the body with every bound lambda name *)
        let _, fvs_body = get_tag_A body in
        let live_vars = StringSet.union fvs_body live_across in
        List.fold_right
          (fun n acc -> add_multiple_edges acc n live_vars)
          bound_names graph
  and helpC
      (cexp : ('a * freevarst) cexpr)
      (live_across : StringSet.t)
      (surrounding : grapht) : grapht =
    match cexp with
    | CIf (_, thn, els, _) ->
        let graph = helpA els live_across surrounding in
        helpA thn live_across graph
    | CLPrim2 (_, _, rhs, _) -> helpA rhs live_across surrounding
    (* No sub-aexprs that exist inside the current environment
       (lambdas make their own environment). *)
    | CLambda (_, _, _, _)
     |CROLambda (_, _, _, _)
     |CPrim1 (_, _, _)
     |CEPrim2 (_, _, _, _)
     |CNativeApp (_, _, _)
     |CApp (_, _, _)
     |CImmExpr _
     |CTuple (_, _)
     |CGetItem (_, _, _)
     |CSetItem (_, _, _, _) -> surrounding
  in
  helpA e StringSet.empty (graph_from_nodes live)
;;

let sl_order (g : grapht) : string list =
  let rec sl_help (degree_map : (string * int) list) (worklist : string list) :
      string list =
    if List.length degree_map == 0 then
      worklist
    else
      let sorted_by_smallest_degree =
        List.sort (fun (_, deg1) (_, deg2) -> Int.compare deg1 deg2) degree_map
      in
      let smallest_degree_node = fst (List.hd sorted_by_smallest_degree) in
      let sd_node_neighbors = get_neighbors g smallest_degree_node in
      let updated_degree_map =
        degree_map
        |> List.map (fun (n, d) ->
               if List.mem n sd_node_neighbors then (n, d - 1) else (n, d) )
        |> List.remove_assoc smallest_degree_node
      in
      sl_help updated_degree_map (smallest_degree_node :: worklist)
  in
  sl_help (node_degree_map_of g) []
;;

let color_graph (g : grapht) (init_env : int name_envt) : int name_envt =
  let sl_ordering = sl_order g in
  let all_colors = iota (List.length sl_ordering) in
  List.fold_left
    (fun acc_env node ->
      match List.assoc_opt node acc_env with
      (* If node is already in acc_env (a pre-allocated function
         argument) don't allocate it again. *)
      | Some _ -> acc_env
      | None ->
          let neighbors = get_neighbors g node in
          let min_neighbor_color =
            (* Remove all colors assigned to neighbors, take the first
               remaining *)
            List.hd
              (List.fold_right
                 (fun nei remaining_colors ->
                   match List.assoc_opt nei acc_env with
                   | Some color ->
                       List.filter (fun c -> c != color) remaining_colors
                   | None -> remaining_colors )
                 neighbors all_colors )
          in
          (node, min_neighbor_color) :: acc_env )
    init_env sl_ordering
;;

(*
   ....
   -3: RBP + 40
   -2: RBP + 32
   -1: RBP + 24
   0: RBP - 8
   1: RBP - 16
   2: RBP - 24
   ....
 *)
let color_to_reg (color : int) : arg =
  match color with
  | _ when color < 0 ->
      (* Function arguments above the RBP *)
      let offset = ~-color + 2 in
      RegOffset (word_size * offset, RBP)
  | _ when color < num_scratch_regs -> Reg (List.nth allocated_registers color)
  | _ ->
      (* Spill to stack *)
      let offset = ~-(color - num_scratch_regs + 1) in
      RegOffset (word_size * offset, RBP)
;;

let colors_to_regs (colors : int name_envt) : arg name_envt =
  List.map (fun (n, c) -> (n, color_to_reg c)) colors
;;

let register_allocation (prog : tag aprogram) :
    tag aprogram * arg name_envt tag_envt =
  let rec allocate_aexpr (expr : (tag * freevarst) aexpr) :
      arg name_envt tag_envt =
    match expr with
    | ALet (_, bind, body, _) ->
        let bind_closure_env = allocate_cexpr bind in
        let body_closure_env = allocate_aexpr body in
        bind_closure_env @ body_closure_env
    | ASeq (left, right, _) ->
        let left_closure_env = allocate_cexpr left in
        let right_closure_env = allocate_aexpr right in
        left_closure_env @ right_closure_env
    | ACExpr expr -> allocate_cexpr expr
    | ALetRec (bindings, body, _) ->
        let bindings_closure_env =
          flat_map (fun (_, exp) -> allocate_cexpr exp) bindings
        in
        let body_closure_env = allocate_aexpr body in
        bindings_closure_env @ body_closure_env
  and allocate_cexpr (expr : (tag * freevarst) cexpr) : arg name_envt tag_envt =
    match expr with
    | CIf (_, thn, els, _) ->
        let thn_closure_env = allocate_aexpr thn in
        let els_closure_env = allocate_aexpr els in
        thn_closure_env @ els_closure_env
    | CLPrim2 (_, _, rhs, _) -> allocate_aexpr rhs
    | CROLambda (_, args, body, (tag, fvs)) | CLambda (args, body, _, (tag, fvs))
      ->
        let arg_env = List.mapi (fun i s -> (s, ~-(i + 1))) args in
        let interference_graph =
          interfere body (StringSet.union fvs (StringSet.of_list args))
        in
        let colored_graph = color_graph interference_graph arg_env in
        let allocated_envt = colors_to_regs colored_graph in
        let closure_envs = allocate_aexpr body in
        (tag, allocated_envt) :: closure_envs
    (* These all have immediate arguments, which have already been
       allocated if necessary. *)
    | CPrim1 (_, _, _)
     |CEPrim2 (_, _, _, _)
     |CNativeApp (_, _, _)
     |CApp (_, _, _)
     |CImmExpr _
     |CTuple (_, _)
     |CGetItem (_, _, _)
     |CSetItem (_, _, _, _) -> []
  in
  let allocate_env (prog : (tag * freevarst) aprogram) : arg name_envt tag_envt
      =
    match prog with
    | AProgram (expr, _, (tag, _)) ->
        let interference_graph = interfere expr StringSet.empty in
        let allocated_envt =
          colors_to_regs (color_graph interference_graph [])
        in
        let closure_envs = allocate_aexpr expr in
        (tag, allocated_envt) :: closure_envs
  in
  let fvs_annotated_prog = annotate_with_free_vars prog in
  (prog, allocate_env fvs_annotated_prog)
;;
