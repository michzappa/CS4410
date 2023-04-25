(* Simple accumulation of duplicates in a list.
   This is inefficient however are not focused on performance. *)
let collect_duplicates (loa : 'a list) : 'a list =
  let rec cda loa acc =
    match loa with
    (* Base case returns the accumulator *)
    | [] | [_] -> acc
    (* If name already acc then skip *)
    | f :: r when List.mem f acc -> cda r acc
    (* If name is in the rest of the list, then append and continue *)
    | f :: r when List.mem f r -> cda r (f :: acc)
    (* Name is unique or was already caught earlier, continue *)
    | _ :: r -> cda r acc
  in
  List.rev (cda loa [])
;;

let raise_if (b : bool) e : unit = if b then raise e else ()

let enumerate (loa : 'a list) : (int * 'a) list =
  let rec enum_help loa c =
    match loa with
    | [] -> []
    | f :: r -> (c, f) :: enum_help r (c + 1)
  in
  enum_help loa 0
;;

let iota (n : int) : int list = List.init n Fun.id

let split_at (idx : int) (loa : 'a list) : 'a list * 'a list =
  raise_if (idx < 0) (Invalid_argument "negative idx passed to split_at");
  let rec split_at_acc idx loa acc =
    match (idx, loa) with
    | _, [] | 0, _ -> (List.rev acc, loa)
    | _, f :: rest -> split_at_acc (idx - 1) rest (f :: acc)
  in
  split_at_acc idx loa []
;;

let flat_map (f : 'a -> 'b list) (l : 'a list) : 'b list =
  l |> List.map f |> List.flatten
;;

let flat_mapi (f : int -> 'a -> 'b list) (l : 'a list) : 'b list =
  l |> List.mapi f |> List.flatten
;;

let flat_rev_map (f : 'a -> 'b list) (l : 'a list) : 'b list =
  l |> List.rev_map f |> List.flatten
;;

module StringSet = Set.Make (String)

let rec replicate x i = if i = 0 then [] else x :: replicate x (i - 1)

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
  | [] -> false
  | x :: xs -> elt = x || find_one xs elt
;;

let rec find_dup (l : 'a list) : 'a option =
  match l with
  | [] -> None
  | [_] -> None
  | x :: xs -> if find_one xs x then Some x else find_dup xs
;;
