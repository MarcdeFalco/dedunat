type term =
    | Var of string
    | Function of string * term list

type formula =
    | PropVar of string
    | Rel of string * term list
    | Or of formula * formula
    | And of formula * formula
    | Not of formula
    | Implies of formula * formula
    | Forall of string * formula
    | Exists of string * formula
    | Absurd

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


let rec string_of_formula f =
    let aux f = 
        let s = string_of_formula f in
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
    | Forall(x,f) -> "\\-/"^x^". "^string_of_formula f
    | Exists(x,f) -> "-)"^x^". "^string_of_formula f

let pretty_print f =
    print_string (string_of_formula f);
    print_newline ()
