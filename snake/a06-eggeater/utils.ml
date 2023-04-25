open Errors

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

let split_at (idx : int) (loa : 'a list) : 'a list * 'a list =
  raise_if (idx < 0) (InternalCompilerError "negative idx passed to split_at");
  let rec split_at_acc idx loa acc =
    match (idx, loa) with
    | _, [] | 0, _ -> (List.rev acc, loa)
    | _, f :: rest -> split_at_acc (idx - 1) rest (f :: acc)
  in
  split_at_acc idx loa []
;;
