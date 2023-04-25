open Printf
module NeighborSet = Set.Make (String)

type neighborst = NeighborSet.t

module Graph = Map.Make (String)

type grapht = neighborst Graph.t

module StringSet = Set.Make (String)

type freevarst = StringSet.t

let empty : grapht = Graph.empty

let add_node (g : grapht) (name : string) : grapht =
  if Graph.mem name g then g else Graph.add name NeighborSet.empty g
;;

let add_directed_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_node (add_node g n1) n2 in
  let curr_neighbors = Graph.find n1 g' in
  Graph.add n1 (NeighborSet.add n2 curr_neighbors) g'
;;

let add_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  if n1 = n2 then
    g
  else
    let g' = add_directed_edge g n1 n2 in
    add_directed_edge g' n2 n1
;;

let add_multiple_edges (graph : grapht) (node : string) (neighbors : StringSet.t)
    =
  StringSet.fold
    (fun n acc -> add_edge acc node n)
    neighbors (add_node graph node)
;;

let get_neighbors (g : grapht) (name : string) : string list =
  if Graph.mem name g then
    NeighborSet.fold (fun n ns -> n :: ns) (Graph.find name g) []
  else
    []
;;

let get_degree (g : grapht) (node : string) : int =
  List.length (get_neighbors g node)
;;

let get_vertices (g : grapht) : string list =
  let keys, _ = List.split (Graph.bindings g) in
  keys
;;

let string_of_graph (g : grapht) : string =
  let string_of_neighbors (n : string) : string =
    ExtString.String.join ", " (get_neighbors g n)
  in
  ExtString.String.join "\n"
    (List.map
       (fun k -> sprintf "%s: %s" k (string_of_neighbors k))
       (get_vertices g) )
  ^ "\n"
;;

let graph_equal (g1 : grapht) (g2 : grapht) : bool =
  Graph.equal NeighborSet.equal g1 g2
;;

let graph_from_nodes ?(init_graph : grapht = empty) (nodes : StringSet.t) :
    grapht =
  StringSet.fold (fun s acc -> add_multiple_edges acc s nodes) nodes init_graph
;;

let graph_from_node_verts_list (nvl : (string * string list) list) : grapht =
  List.fold_right
    (fun (node, verts) acc ->
      List.fold_right
        (fun vert acc -> add_edge acc node vert)
        verts (add_node acc node) )
    nvl empty
;;

let node_degree_map_of (g : grapht) : (string * int) list =
  List.fold_right (fun n acc -> (n, get_degree g n) :: acc) (get_vertices g) []
;;
