type operator =
  | OpAnd
  | OpOr
  | OpImplies
  | OpNot
  | OpForall
  | OpExists
  | OpAbsurd

type term = Var of string | Function of string * term list

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
  | Function (f, tl) -> Function (f, List.map (subst_term x tx) tl)

let rec subst x t f =
  match f with
  | And (f1, f2) -> And (subst x t f1, subst x t f2)
  | Or (f1, f2) -> Or (subst x t f1, subst x t f2)
  | Implies (f1, f2) -> Implies (subst x t f1, subst x t f2)
  | Not f -> Not (subst x t f)
  | Forall (y, f) -> Forall (y, if x = y then f else subst x t f)
  | Exists (y, f) -> Exists (y, if x = y then f else subst x t f)
  | Rel (r, tl) -> Rel (r, List.map (subst_term x t) tl)
  | _ -> f

let rec rev_subst_term x tx t =
  if t = tx then Var x
  else
    match t with
    | Var y -> Var y
    | Function (f, tl) -> Function (f, List.map (rev_subst_term x tx) tl)

let rec rev_subst x t f =
  match f with
  | And (f1, f2) -> And (rev_subst x t f1, rev_subst x t f2)
  | Or (f1, f2) -> Or (rev_subst x t f1, rev_subst x t f2)
  | Implies (f1, f2) -> Implies (rev_subst x t f1, rev_subst x t f2)
  | Not f -> Not (rev_subst x t f)
  | Forall (y, f) -> Forall (y, if x = y then f else rev_subst x t f)
  | Exists (y, f) -> Exists (y, if x = y then f else rev_subst x t f)
  | Rel (r, tl) -> Rel (r, List.map (rev_subst_term x t) tl)
  | _ -> f

type definition = string * int * formula

let rec apply_def def f =
  let name, arity, subf = def in
  match f with
  | And (f1, f2) -> And (apply_def def f1, apply_def def f2)
  | Or (f1, f2) -> Or (apply_def def f1, apply_def def f2)
  | Implies (f1, f2) -> Implies (apply_def def f1, apply_def def f2)
  | Not f -> Not (apply_def def f)
  | Forall (y, f) -> Forall (y, apply_def def f)
  | Exists (y, f) -> Exists (y, apply_def def f)
  | Rel (r, tl) when r = name && List.length tl = arity ->
      let args = List.init arity (fun i -> "V" ^ string_of_int (i + 1)) in
      let zip = List.combine args tl in
      List.fold_left (fun f (x, t) -> subst x t f) subf zip
  | _ -> f

let alpha_rep f =
  (* find a distinguished alpha-equivalent formula
     by using fresh names - here, we force identifiers to start
     with a letter, therefore, we can use numbers to substitute
     If its' the nth quantifier encountered
     \-/x.f will become \-/n.f[x\n] *)
  let counter = ref 0 in
  let rec aux f =
    match f with
    | And (f1, f2) -> And (aux f1, aux f2)
    | Or (f1, f2) -> Or (aux f1, aux f2)
    | Implies (f1, f2) -> Implies (aux f1, aux f2)
    | Not f -> Not (aux f)
    | Forall (x, f) ->
        let fresh = string_of_int !counter in
        incr counter;
        Forall (fresh, subst x (Var fresh) f)
    | Exists (x, f) ->
        let fresh = string_of_int !counter in
        incr counter;
        Exists (fresh, subst x (Var fresh) f)
    | _ -> f
  in
  aux f

let alpha_equivalent f1 f2 = alpha_rep f1 = alpha_rep f2

let rec mem_alpha f l =
  match l with [] -> false | g :: q -> alpha_equivalent f g || mem_alpha f q
