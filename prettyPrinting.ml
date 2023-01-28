open Deduction
open Formula

let ascii_string_of_operator op =
  match op with
  | OpAnd -> "/\\"
  | OpOr -> "\\/"
  | OpImplies -> "->"
  | OpNot -> "~"
  | OpForall -> "\\-/"
  | OpExists -> "-]"
  | OpAbsurd -> "_|_"

let unicode_string_of_operator op =
  match op with
  | OpAnd -> "∧"
  | OpOr -> "∨"
  | OpImplies -> "→"
  | OpNot -> "¬"
  | OpForall -> "∀"
  | OpExists -> "∃"
  | OpAbsurd -> "⟂"

let string_of_operator op =
  if Config.is_ascii () then ascii_string_of_operator op
  else unicode_string_of_operator op

let rec string_of_term t =
  match t with
  | Var x -> x
  | Function (f, xl) -> f ^ "(" ^ string_of_term_list xl ^ ")"

and string_of_term_list f = String.concat ", " (List.map string_of_term f)

let simple f =
  match f with
  | Or _ | And _ | Implies _ | Forall _ | Exists _ -> false
  | _ -> true

let rec latex_of_formula f =
  let aux f =
    let s = latex_of_formula f in
    if simple f then s else "(" ^ s ^ ")"
  in
  match f with
  | PropVar x -> x
  | Rel (r, tl) -> r ^ "(" ^ string_of_term_list tl ^ ")"
  | Or (f1, f2) -> aux f1 ^ " \\vee " ^ aux f2
  | And (f1, f2) -> aux f1 ^ " \\wedge " ^ aux f2
  | Implies (f1, f2) -> aux f1 ^ " \\rightarrow " ^ aux f2
  | Not f -> "\\neg " ^ aux f
  | Absurd -> "\\perp"
  | Forall (x, f) -> "\\forall " ^ x ^ ". " ^ latex_of_formula f
  | Exists (x, f) -> "\\exists " ^ x ^ ". " ^ latex_of_formula f

let rec unicode_string_of_formula f =
  let aux f =
    let s = unicode_string_of_formula f in
    if simple f then s else "(" ^ s ^ ")"
  in
  match f with
  | PropVar x -> x
  | Rel (r, tl) -> r ^ "(" ^ string_of_term_list tl ^ ")"
  | Or (f1, f2) -> aux f1 ^ " ∨ " ^ aux f2
  | And (f1, f2) -> aux f1 ^ " ∧ " ^ aux f2
  | Implies (f1, f2) -> aux f1 ^ " → " ^ aux f2
  | Not f -> "¬" ^ aux f
  | Absurd -> "⟂"
  | Forall (x, f) -> "∀" ^ x ^ ". " ^ unicode_string_of_formula f
  | Exists (x, f) -> "∃" ^ x ^ ". " ^ unicode_string_of_formula f

let rec ascii_string_of_formula f =
  let aux f =
    let s = ascii_string_of_formula f in
    if simple f then s else "(" ^ s ^ ")"
  in
  match f with
  | PropVar x -> x
  | Rel (r, tl) -> r ^ "(" ^ string_of_term_list tl ^ ")"
  | Or (f1, f2) -> aux f1 ^ " \\/ " ^ aux f2
  | And (f1, f2) -> aux f1 ^ " /\\ " ^ aux f2
  | Implies (f1, f2) -> aux f1 ^ " -> " ^ aux f2
  | Not f -> "~" ^ aux f
  | Absurd -> "_|_"
  | Forall (x, f) -> "\\-/" ^ x ^ ". " ^ ascii_string_of_formula f
  | Exists (x, f) -> "-]" ^ x ^ ". " ^ ascii_string_of_formula f

let string_of_formula f =
  if Config.is_ascii () then ascii_string_of_formula f
  else unicode_string_of_formula f

let pretty_print f =
  print_string (string_of_formula f);
  print_newline ()

let string_of_sequent (fl, f) =
  String.concat ", " (List.map string_of_formula fl)
  ^ (if Config.is_ascii () then " |- " else " ⊢ ")
  ^ string_of_formula f

let string_of_proof p =
  let add_spaces l =
    (* takes a list of string and add spaces left/right to get a matrix of strings *)
    let max_length = List.fold_left max 0 (List.map U8string.length l) in
    List.map
      (fun s ->
        let n = max_length - U8string.length s in
        let n_left = n / 2 in
        let n_right = n - n_left in
        let spaces_left = String.make n_left ' ' in
        let spaces_right = String.make n_right ' ' in
        spaces_left ^ s ^ spaces_right)
      l
  in
  let add_empty ll =
    (* takes a list of list of strings and ensures they are
       all of the same length adding "" if needed *)
    let max_length = List.fold_left max 0 (List.map List.length ll) in
    List.map
      (fun l ->
        add_spaces (l @ List.init (max_length - List.length l) (fun _ -> "")))
      ll
  in
  let rec fusion ll =
    (* takes a list of list of string where every sublists is of the same
       length and concatenates all first strings, then all second
       strings... *)
    match ll with
    | [] -> []
    | [] :: _ -> []
    | _ ->
        String.concat "  " (List.map List.hd ll) :: fusion (List.map List.tl ll)
  in
  let auxr_ascii r =
    match r with
    | ElimImplies _ -> "->e"
    | IntroImplies -> "->i"
    | ElimAnd (true, _) -> "/\\eg"
    | ElimAnd (false, _) -> "/\\ed"
    | IntroAnd -> "/\\i"
    | IntroOr true -> "\\/ig"
    | IntroOr false -> "\\/id"
    | ElimOr _ -> "\\/e"
    | ElimNot _ -> "~e"
    | IntroNot -> "~i"
    | IntroForall _ -> "\\-/i"
    | ElimForall _ -> "\\-/e"
    | IntroExists _ -> "-]i"
    | ElimExists _ -> "-]e"
    | ElimAbsurd -> "_|_e"
    | Assume -> "!"
    | Axiom -> "ax"
    | Peirce -> "pi"
    | Classical -> "cl"
    | Unfinished -> "*"
  in
  let auxr_unicode r =
    match r with
    | ElimImplies _ -> "→e"
    | IntroImplies -> "→i"
    | ElimAnd (true, _) -> "∧eg"
    | ElimAnd (false, _) -> "∧ed"
    | IntroAnd -> "∧i"
    | IntroOr true -> "∨ig"
    | IntroOr false -> "∨id"
    | ElimOr _ -> "∨e"
    | ElimNot _ -> "¬e"
    | IntroNot -> "¬i"
    | IntroForall _ -> "∀i"
    | ElimForall _ -> "∀e"
    | IntroExists _ -> "∃i"
    | ElimExists _ -> "∃e"
    | ElimAbsurd -> "⟂e"
    | Assume -> "!"
    | Axiom -> "ax"
    | Peirce -> "pi"
    | Classical -> "cl"
    | Unfinished -> "*"
  in

  let auxr = if Config.is_ascii () then auxr_ascii else auxr_unicode in

  let rec aux (Inference (seq, pl, r)) =
    let sseq = string_of_sequent seq in
    let aux_pl = add_empty (List.map aux pl) in
    let lpl = fusion aux_pl in
    let n =
      max (U8string.length sseq)
        (List.fold_left max 0 (List.map U8string.length lpl))
    in
    let sep =
      if r = Unfinished then
        U8string.make n (if Config.is_ascii () then "*" else "░")
      else U8string.make n (if Config.is_ascii () then "-" else "─") ^ auxr r
    in
    let l = sseq :: sep :: lpl in
    add_spaces l
  in
  String.concat "\n" (aux p |> List.rev)

let latex_of_proof p =
  let s = "\\def\\fCenter{\\mbox{\\ $\\vdash$\\ }}\n" in
  let auxr r =
    "\\RightLabel{$"
    ^ (match r with
      | ElimImplies _ -> "\\rightarrow_e"
      | IntroImplies -> "\\rightarrow_i"
      | ElimAnd (true, _) -> "\\wedge_{e g}"
      | ElimAnd (false, _) -> "\\wedge_{e d}"
      | IntroAnd -> "\\wedge_i"
      | IntroOr true -> "\\vee_{i g}"
      | IntroOr false -> "\\vee_{i d}"
      | ElimOr _ -> "\\vee_e"
      | ElimNot _ -> "\\neg_e"
      | IntroNot -> "\\neg_i"
      | IntroForall _ -> "\\forall_i"
      | ElimForall _ -> "\\forall_e"
      | IntroExists _ -> "\\exists_i"
      | ElimExists _ -> "\\exists_e"
      | ElimAbsurd -> "\\perp_e"
      | Assume -> "!"
      | Axiom -> "ax"
      | Peirce -> "pi"
      | Classical -> "cl"
      | Unfinished -> "*")
    ^ "$}\n"
  in

  let rec auxl pl =
    match pl with
    | [] -> "\\AxiomC{}\n"
    | _ -> String.concat "" (List.map aux pl)
  and aux (Inference (seq, pl, r)) =
    let gamma, f = seq in
    let l_seq =
      String.concat ", " (List.map latex_of_formula gamma)
      ^ " \\fCenter " ^ latex_of_formula f
    in
    auxl pl ^ auxr r ^ "\\"
    ^ (match List.length pl with
      | 0 | 1 -> "Unary"
      | 2 -> "Binary"
      | _ -> "Trinary")
    ^ "Inf$" ^ l_seq ^ "$\n"
  in
  s ^ aux p ^ "\\DisplayProof\n"

let frenchmath_of_proof p =
  let (Inference (seq, _, _)) = p in
  let lines = Stack.create () in
  let level = ref 0 in
  let add_line s = Stack.push (String.make !level ' ' ^ s) lines in
  let hyp, f = seq in
  add_line
    (Printf.sprintf "Théorème : %son a %s"
       (if hyp = [] then ""
       else
         "Si "
         ^ String.concat " et " (List.map string_of_formula hyp)
         ^ ", alors ")
       (string_of_formula f));
  let rec aux (Inference (seq, pl, r)) =
    match r with
    | IntroAnd -> (
        let _, f = seq in
        match (pl, f) with
        | [ pa; pb ], And (a, b) ->
            add_line (Printf.sprintf "Montrons %s :" (string_of_formula a));
            incr level;
            aux pa;
            decr level;
            add_line (Printf.sprintf "Montrons %s :" (string_of_formula b));
            incr level;
            aux pb;
            decr level;
            add_line (Printf.sprintf "On a donc %s." (string_of_formula f))
        | _ -> failwith "impossible")
    | ElimAnd _ ->
        let _, f = seq in
        List.iter aux pl;
        add_line (Printf.sprintf "On a ainsi %s." (string_of_formula f))
    | IntroOr _ ->
        let _, f = seq in
        List.iter aux pl;
        add_line (Printf.sprintf "On a ainsi %s." (string_of_formula f))
    | ElimOr (a, b) -> (
        let _, f = seq in
        match pl with
        | [ pcond; pa; pb ] ->
            add_line
              (Printf.sprintf "Montrons la disjonction : %s."
                 (string_of_formula (Or (a, b))));
            incr level;
            aux pcond;
            decr level;
            add_line "On peut alors faire une disjonction de cas.";
            add_line
              (Printf.sprintf "Premier cas : on suppose %s."
                 (string_of_formula a));
            incr level;
            aux pa;
            decr level;
            add_line
              (Printf.sprintf "Second cas : on suppose %s."
                 (string_of_formula b));
            incr level;
            aux pb;
            decr level;
            add_line
              (Printf.sprintf "On a bien montré %s dans tous les cas."
                 (string_of_formula f))
        | _ -> failwith "impossible")
    | IntroImplies -> (
        match seq with
        | _, Implies (f, g) ->
            add_line (Printf.sprintf "Supposons %s." (string_of_formula f));
            incr level;
            List.iter aux pl;
            decr level;
            add_line
              (Printf.sprintf "On a montré %s. Donc %s est vrai."
                 (string_of_formula g)
                 (string_of_formula (Implies (f, g))))
        | _ -> failwith "impossible")
    | ElimImplies f -> (
        let _, g = seq in
        match pl with
        | [ pimp; phyp ] ->
            add_line
              (Printf.sprintf "Montrons que de %s on peut déduire %s :"
                 (string_of_formula f) (string_of_formula g));
            incr level;
            aux pimp;
            decr level;
            add_line
              (Printf.sprintf "On va maintenant montrer %s :"
                 (string_of_formula f));
            incr level;
            aux phyp;
            decr level;
            add_line
              (Printf.sprintf "On peut ainsi en déduire %s."
                 (string_of_formula g))
        | _ -> failwith "impossible")
    | ElimAbsurd ->
        add_line "Montrons qu'on peut alors aboutir à une contradiction."
    | IntroForall x -> (
        match pl with
        | [ p ] ->
            add_line (Printf.sprintf "Soit %s." x);
            aux p
        | _ -> failwith "impossible")
    | ElimForall (x, t) -> (
        let _, f = seq in
        match pl with
        | [ p ] ->
            add_line
              (Printf.sprintf "Montrons que pour tout %s, on a %s." x
                 (Formula.rev_subst x t f |> string_of_formula));
            incr level;
            aux p;
            decr level;
            add_line
              (Printf.sprintf "Ainsi, on peut en déduire %s pour %s = %s."
                 (string_of_formula f) x (string_of_term t))
        | _ -> failwith "impossible")
    | IntroExists t -> (
        let _, f = seq in
        match f with
        | Exists (x, _) ->
            add_line (Printf.sprintf "On pose %s = %s." x (string_of_term t));
            incr level;
            List.iter aux pl;
            decr level
        | _ -> failwith "impossible")
    | ElimExists (x, f) -> (
        match pl with
        | [ pex; p ] ->
            add_line
              (Printf.sprintf "On va montrer qu'il existe un %s tel que %s." x
                 (string_of_formula f));
            incr level;
            aux pex;
            decr level;
            add_line
              (Printf.sprintf "On peut donc supposer %s." (string_of_formula f));
            incr level;
            aux p;
            decr level
        | _ -> failwith "impossible")
    | Assume ->
        let _, f = seq in
        add_line (Printf.sprintf "On admet %s." (string_of_formula f))
    | Classical ->
        let _, f = seq in
        add_line
          (Printf.sprintf "En vertu du tiers exclu, on a %s."
             (string_of_formula f))
    | Peirce ->
        let _, f = seq in
        add_line
          (Printf.sprintf "En vertu de la loi de Peirce, on a %s."
             (string_of_formula f))
    | Axiom ->
        let _, f = seq in
        add_line
          (Printf.sprintf "En vertu des hypothèses, on a %s."
             (string_of_formula f))
    | _ -> ()
  in
  aux p;
  add_line "CQFD";
  String.concat "\n" (List.rev (List.of_seq (Stack.to_seq lines)))
