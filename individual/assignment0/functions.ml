(* return the maximum of two integers *)
let max (n : int) (m : int) : int =
  if n > m then n else m

(* return the nth fibonacci number where n = 1 is the first fibonacci
   index *)
let rec fibonacci (n : int) : int =
  if n < 3 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

(* fibonacci 3 *)
(* if 3 < 3 then 1 else fibonacci (3 - 1) + fibonacci (3 - 2) *)
(* if false then 1 else fibonacci (3 - 1) + fibonacci (3 - 2) *)
(* fibonacci (3 - 1) + fibonacci (3 - 2) *)
(* fibonacci 2 + fibonacci 1 *)
(* (if 2 < 3 then 1 else fibonacci (2 - 1) + fibonacci (2 - 2)) + (if 1 < 3 then 1 else fibonacci (1 - 1) + fibonacci (1 - 2)) *)
(* (if true  then 1 else fibonacci (2 - 1) + fibonacci (2 - 2)) + (if true  then 1 else fibonacci (1 - 1) + fibonacci (1 - 2)) *)
(* 1 + 1 *)
(* 2 *)

(* binary tree of strings *)
type btnode = Leaf | Node of string * btnode * btnode

(* return the string containing a btnode's Node's values in
   left-to-right order *)
let rec inorder_str (bt : btnode) : string =
  match bt with
  | Leaf -> ""
  | Node (s, left, right) -> inorder_str left ^ s ^ inorder_str right

(* inorder_str (Node ("a", Node ("b", Leaf, Leaf), Node ("c", Leaf, Leaf))) *)
(* match (Node ("a", Node ("b", Leaf, Leaf), Node ("c", Leaf, Leaf))) with
   | Leaf -> ""
   | Node (s, left, right) -> inorder_str left ^ s ^ inorder_str right *)
(* inorder_str (Node ("b", Leaf, Leaf)) ^ "a" ^ inorder_str (Node ("c", Leaf, Leaf)) *)
(* (match (Node ("b", Leaf, Leaf)) with
    | Leaf -> ""
    | Node (s, left, right) -> inorder_str left ^ s ^ inorder_str right)
   ^ "a" ^
   (match (Node ("c", Leaf, Leaf)) with
    | Leaf -> ""
    | Node (s, left, right) -> inorder_str left ^ s ^ inorder_str right) *)
(* (inorder_str Leaf ^ "b" ^ inorder_str Leaf) ^ "a" ^ (inorder_str Leaf ^ "c" ^ inorder_str Leaf) *)
(* ((match Leaf with
     | Leaf -> ""
     | Node (s, left, right) -> inorder_str left ^ s ^ inorder_str right)
    ^ "b" ^
    (match Leaf with
     | Leaf -> ""
     | Node (s, left, right) -> inorder_str left ^ s ^ inorder_str right))
     ^ "a" ^
    ((match Leaf with
     | Leaf -> ""
     | Node (s, left, right) -> inorder_str left ^ s ^ inorder_str right)
    ^ "c" ^
    (match Leaf with
     | Leaf -> ""
     | Node (s, left, right) -> inorder_str left ^ s ^ inorder_str right)) *)
(* ("" ^ "b" ^ "") ^ "a" ^ ("" ^ "c" ^ "") *)
(* "bac" *)

(* return the number of Node's in a btnode *)
let rec size (bt : btnode) : int =
  match bt with
  | Leaf -> 0
  | Node (s, left, right) -> 1 + size left + size right

(* return the height of a btnode, where Leaf has no height because they
   don't have a value. *)
let rec height (bt : btnode) : int =
  match bt with
  | Leaf -> 0
  | Node (s, left, right) -> 1 + max (height left) (height right)

(* return the result of incrementing every element in the given list
   by 1 *)
let rec increment_all (l : int list) : int list =
  match l with
  | [] -> []
  | first :: rest -> (first + 1) :: increment_all rest

(* return the result of filtering the given list for strings of length
   greater than n *)
let rec long_strings (l : string list) (n : int) =
  match l with
  | [] -> []
  | first :: rest ->
     if String.length first > n then first :: long_strings rest n
     else long_strings rest n

(* return the list containing every other element from the given
   list *)
let every_other (l : 'a list) =
  let rec every_other' (l2 : 'a list) (take : bool) =
    match l2 with
    | [] -> []
    | first :: rest ->
       if take then first :: every_other' rest (not take)
       else every_other' rest (not take)
  in every_other' l true

(* return the list containing the sums of the sub-lists of the given
   list *)
let rec sum_all (ll : int list list) : int list =
  let rec sum (l : int list) : int =
    match l with
    | [] -> 0
    | first :: rest -> first + (sum rest) in
  match ll with
  | [] -> []
  | first :: rest -> (sum first) :: (sum_all rest)
