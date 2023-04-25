let rec find ls x =
  match ls with
  | [] ->
      raise (Errors.InternalCompilerError (Printf.sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
  | [] -> false
  | x :: xs -> elt = x || find_one xs elt
;;

let rec find_dup (l : 'a list) : 'a option =
  match l with
  | [] -> None
  | [_] -> None
  | x :: xs ->
      if find_one xs x then
        Some x
      else
        find_dup xs
;;

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

let raise_if (b : bool) e : unit =
  if b then
    raise e
  else
    ()
;;

let enumerate (loa : 'a list) : (int * 'a) list =
  let rec enum_help loa c =
    match loa with
    | [] -> []
    | f :: r -> (c, f) :: enum_help r (c + 1)
  in
  enum_help loa 0
;;
