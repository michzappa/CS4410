let rec parse_toks (toks : pos tok list) : (pos sexp list, string) result =
  match toks with
  | [] -> Ok[]
  | (LPAREN p) :: rest ->
     (match parse_list rest [] with
      | (p_end, sexps, []) -> Ok[Nest (sexps, pos_diff p p_end)]
      | (_, _ , rem) -> Error "Unmatched SOMETHING")
  | (RPAREN p) :: rest -> Error (sprintf "Unmatched right paren at %s" (pos_to_string p false))
  | atom :: rest ->
     (match parse_toks rest with
      | Ok(sexps) -> Ok((parse_atom atom) :: sexps)
      | e -> e)
  (* | (TSym (sym, p)) :: rest -> Error (sprintf "Found %s at %s, expect '('" sym (pos_to_string p false)) *)
  (* | (TInt (num, p)) :: rest -> Error (sprintf "Found %d at %s, expect '('" num (pos_to_string p false)) *)
  (* | (TBool (bl, p)) :: rest -> Error (sprintf "Found %b at %s, expect '('" bl (pos_to_string p false)) *)
and parse_list (toks : pos tok list) (sofar : pos sexp list) : (pos * pos sexp list * pos tok list)  =
  (* Returns the position of the closing right paren, the list of *)
     (* contained sexps, and the remaining tokens to be parsed. *)
  match toks with
  | [] -> ((0,0,0,0), sofar, [])
  | (LPAREN p) :: rest ->
     (match parse_list rest [] with
      | (p_end, sexps, []) -> (p_end, sofar @ [Nest(sexps, pos_diff p p_end)], [])
      | (p_end, sexps, rem) ->
         failwith "blah"
         (* (match parse_list rem [] with *)
         (*  | (rem_p_end, rem_sexps, []) -> *)
         (*     (rem_p_end, sofar @ [Nest(sexps, pos_diff p p_end)] @ rem_sexps, []) *)
         (*  | (_, _ , rem) -> failwith "there shouldn't be any tokens remaining") *)
     )
  (* | [(RPAREN p)] -> (p, sofar, []) *)
  | (RPAREN p) :: rest -> (p, sofar, rest)
  (* | [atom] -> failwith "unmatched" (\* TODO work this into the branch for LPAREN *\) *)
  | atom :: rest -> parse_list rest (sofar @ [parse_atom atom])
and parse_atom (atom: pos tok) : pos sexp =
  (match atom with
   | (TSym (sym, p)) -> (Sym (sym, p))
   | (TInt (num, p)) -> (Int (num, p))
   | (TBool (bl, p)) -> (Bool (bl, p))
   | _ -> failwith "not an atom")
;;

(parse_toks (tokenize "(a (b true) 3)"))
