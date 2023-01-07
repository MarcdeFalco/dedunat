type term =
    | Var of string
    | Function of string * term list

type formula =
    | PropVar of string
    | Rel of string * term list
    | Implies of formula * formula
    | Or of formula * formula
    | And of formula * formula
    | Not of formula
    | Forall of string * formula
    | Exists of string * formula
    | Absurd

let rec subst_term x tx t =
    match t with
    | Var y -> if x = y then tx else t
    | Function(f, tl) -> Function(f, List.map (subst_term x tx) tl)

let rec subst x t f =
    match f with

    | And(f1,f2) -> And(subst x t f1, subst x t f2)
    | Or(f1,f2) -> Or(subst x t f1, subst x t f2)
    | Implies(f1,f2) -> Implies(subst x t f1, subst x t f2)
    | Not f -> Not (subst x t f)

    | Forall(y, f) -> Forall(y, if x = y then f else subst x t f)
    | Exists(y, f) -> Exists(y, if x = y then f else subst x t f)

    | Rel(r, tl) -> Rel(r, List.map (subst_term x t) tl)

    | _ -> f

let rec rev_subst_term x tx t =
    if t = tx
    then Var x
    else match t with
        | Var y -> Var y
        | Function(f, tl) -> Function(f, List.map (rev_subst_term x tx) tl)

let rec rev_subst x t f =
    match f with

    | And(f1,f2) -> And(rev_subst x t f1, rev_subst x t f2)
    | Or(f1,f2) -> Or(rev_subst x t f1, rev_subst x t f2)
    | Implies(f1,f2) -> Implies(rev_subst x t f1, rev_subst x t f2)
    | Not f -> Not (rev_subst x t f)

    | Forall(y, f) -> Forall(y, if x = y then f else rev_subst x t f)
    | Exists(y, f) -> Exists(y, if x = y then f else rev_subst x t f)

    | Rel(r, tl) -> Rel(r, List.map (rev_subst_term x t) tl)

    | _ -> f

let rec string_of_term t =
    match t with
    | Var x -> x
    | Function(f, xl) ->
        f ^ "(" ^ string_of_term_list xl ^ ")"
and string_of_term_list f =
    String.concat ", "
        (List.map string_of_term f)

let simple f =
    match f with
    | Or _
    | And _
    | Implies _
    | Forall _
    | Exists _ -> false
    | _ -> true

let rec latex_of_formula f =
    let aux f = 
        let s = latex_of_formula f in
        if simple f then s else "("^s^")"
    in
    match f with
    | PropVar x -> x
    | Rel(r,tl) -> r^"("^(string_of_term_list tl)^")"
    | Or(f1,f2) -> aux f1^" \\vee "^aux f2
    | And(f1,f2) -> aux f1^" \\wedge "^aux f2
    | Implies(f1,f2) -> aux f1^" \\rightarrow "^ aux f2
    | Not f -> "\\neg "^aux f
    | Absurd -> "\\perp"
    | Forall(x,f) -> "\\forall"^x^". "^latex_of_formula f
    | Exists(x,f) -> "\\exists"^x^". "^latex_of_formula f

let rec unicode_string_of_formula f =
    let aux f = 
        let s = unicode_string_of_formula f in
        if simple f then s else "("^s^")"
    in
    match f with
    | PropVar x -> x
    | Rel(r,tl) -> r^"("^(string_of_term_list tl)^")"
    | Or(f1,f2) -> aux f1^" ∨ "^aux f2
    | And(f1,f2) -> aux f1^" ∧ "^aux f2
    | Implies(f1,f2) -> aux f1^" → "^ aux f2
    | Not f -> "¬"^aux f
    | Absurd -> "⟂"
    | Forall(x,f) -> "∀"^x^". "^unicode_string_of_formula f
    | Exists(x,f) -> "∃"^x^". "^unicode_string_of_formula f

let rec ascii_string_of_formula f =
    let aux f = 
        let s = ascii_string_of_formula f in
        if simple f then s else "("^s^")"
    in
    match f with
    | PropVar x -> x
    | Rel(r,tl) -> r^"("^(string_of_term_list tl)^")"
    | Or(f1,f2) -> aux f1^" \\/ "^aux f2
    | And(f1,f2) -> aux f1^" /\\ "^aux f2
    | Implies(f1,f2) -> aux f1^" -> "^ aux f2
    | Not f -> "~"^aux f
    | Absurd -> "_|_"
    | Forall(x,f) -> "\\-/"^x^". "^ascii_string_of_formula f
    | Exists(x,f) -> "-]"^x^". "^ascii_string_of_formula f

let string_of_formula f =
  if Config.is_ascii ()
  then ascii_string_of_formula f
  else unicode_string_of_formula f

let pretty_print f =
    print_string (string_of_formula f);
    print_newline ()
