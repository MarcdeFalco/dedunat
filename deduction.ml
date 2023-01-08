open Formula

type rule =
    | ElimOr of formula * formula
    | ElimImplies of formula
    | ElimAnd of bool * formula
    | ElimNot of formula
    | ElimAbsurd
    | ElimForall of string * term
    | ElimExists of string * formula

    | IntroImplies
    | IntroOr of bool
    | IntroAnd
    | IntroNot
    | IntroForall of string
    | IntroExists of term

    | Axiom
    | Classical
    | Pierce

    | Unfinished

type sequent = formula list * formula

let subst_sequent x t (fl, f) =
    (List.map (subst x t) fl, subst x t f)

type proof = Inference of sequent * proof list * rule
type context = sequent list * (proof list -> proof)

let unfinished_proof g =
    Inference(g,[],Unfinished)

let initial_context f =
    [([], f)], fun l -> match l with
        | [p] -> p
        | _ -> failwith "Invalid proof"

let proof_of_context (gl, c) =
    let pl = List.map unfinished_proof gl in
    c pl
    
let string_of_sequent (fl, f) =
    String.concat ", " (List.map string_of_formula fl)
        ^ (if Config.is_ascii () then " |- " else " ⊢ ") 
        ^ string_of_formula f

let string_of_proof p =
    let add_spaces l = (* takes a list of string and add spaces left/right to get a matrix of strings *)
        let max_length = List.fold_left max 0
            (List.map U8string.length l) in
        List.map (fun s ->
            let n = max_length - U8string.length s in
            let n_left = n / 2 in
            let n_right = n - n_left in
            let spaces_left = String.make n_left ' ' in
            let spaces_right = String.make n_right ' ' in
            spaces_left ^ s ^ spaces_right) l
    in
    let add_empty ll = (* takes a list of list of strings and ensures they are
                          all of the same length adding "" if needed *)
        let max_length = List.fold_left max 0
            (List.map List.length ll) in
        List.map (fun l ->
            add_spaces (l 
                @ List.init (max_length - List.length l) (fun _ -> ""))) ll
    in
    let rec fusion ll =
        (* takes a list of list of string where every sublists is of the same
           length and concatenates all first strings, then all second
           strings... *)
        match ll with
        | [] -> []
        | [] :: _ -> []
        | _ -> String.concat "  " (List.map List.hd ll)
               :: fusion (List.map List.tl ll) in
    let auxr_ascii r = match r with
        | ElimImplies _ -> "->e"
        | IntroImplies  -> "->i"

        | ElimAnd (true,_) -> "/\\eg"
        | ElimAnd (false,_) -> "/\\ed"
        | IntroAnd  -> "/\\i"

        | IntroOr true -> "\\/ig"
        | IntroOr false -> "\\/id"
        | ElimOr _ -> "\\/e"

        | ElimNot _ -> "~e"
        | IntroNot -> "~i"

        | IntroForall _ -> "\\-/i"
        | ElimForall _  -> "\\-/e"

        | IntroExists _ -> "-]i"
        | ElimExists _  -> "-]e"

        | ElimAbsurd -> "_|_e"

        | Axiom -> "ax"
        | Pierce -> "pi"
        | Classical -> "cl"

        | Unfinished -> "*" in
     let auxr_unicode r = match r with
        | ElimImplies _ -> "→e"
        | IntroImplies  -> "→i"

        | ElimAnd (true,_) -> "∧eg"
        | ElimAnd (false,_) -> "∧ed"
        | IntroAnd  -> "∧ei"

        | IntroOr true -> "∨ig"
        | IntroOr false -> "∨id"
        | ElimOr _ -> "∨e"

        | ElimNot _ -> "¬e"
        | IntroNot -> "¬i"

        | IntroForall _ -> "∀i"
        | ElimForall _  -> "∀e"

        | IntroExists _ -> "∃i"
        | ElimExists _  -> "∃e"

        | ElimAbsurd -> "⟂"

        | Axiom -> "ax"
        | Pierce -> "pi"
        | Classical -> "cl"

        | Unfinished -> "*" in

    let auxr = if Config.is_ascii () then auxr_ascii else auxr_unicode in

    let rec aux (Inference(seq, pl, r)) =
        let sseq = string_of_sequent seq in
        let aux_pl = add_empty (List.map aux pl) in
        let lpl = fusion aux_pl in
        let n = max (U8string.length sseq)
            (List.fold_left max 0 (List.map U8string.length lpl)) in
        let sep = 
            if r = Unfinished 
            then U8string.make n (if Config.is_ascii () then "*" else "░")
            else U8string.make n (if Config.is_ascii () then "-" else "─") 
            ^ auxr r in
        let l = sseq :: sep :: lpl in
        add_spaces l
    in String.concat "\n" (aux p |> List.rev)


let latex_of_proof p =
    let s = "\\def\\fCenter{\\mbox{\\ $\\vdash$\\ }}\n" in
    let auxr r = "\\RightLabel{$" ^ 
        (match r with
        | ElimImplies _ -> "\\rightarrow_e"
        | IntroImplies  -> "\\rightarrow_i"

        | ElimAnd (true,_) -> "\\wedge_{e g}"
        | ElimAnd (false,_) -> "\\wedge_{e d}"
        | IntroAnd  -> "\\wedge_i"

        | IntroOr true -> "\\vee_{i g}"
        | IntroOr false -> "\\vee_{i d}"
        | ElimOr _ -> "\\vee_e"

        | ElimNot _ -> "\\neg_e"
        | IntroNot -> "\\neg_i"

        | IntroForall _ -> "\\forall_i"
        | ElimForall _  -> "\\forall_e"

        | IntroExists _ -> "\\exists_i"
        | ElimExists _  -> "\\exists_e"

        | ElimAbsurd -> "\\perp_e"

        | Axiom -> "ax"
        | Pierce -> "pi"
        | Classical -> "cl"

        | Unfinished -> "*"

        ) ^ "$}\n" in

    let rec auxl pl =
        match pl with
        | [] -> "\\AxiomC{}\n"
        | _ -> String.concat "" (List.map aux pl)

    and aux (Inference(seq, pl, r)) =
        let gamma, f = seq in
        let l_seq = String.concat ", " (List.map latex_of_formula gamma)
            ^ " \\fCenter " ^ latex_of_formula f in
        auxl pl
        ^ auxr r
        ^ "\\" ^ (match List.length pl with
            | 0 | 1 -> "Unary" | 2 -> "Binary" | _ -> "Trinary")
        ^ "Inf$" ^ l_seq ^ "$\n"
    in s ^ aux p ^ "\\DisplayProof\n"


exception InvalidRule
exception InvalidProof

(* The prover is here. Everything is else is for handling input/output *)
let apply_rule_to_goal r g =
    let build_inference n pl =
        if List.length pl <> n
        then raise InvalidProof
        else Inference(g, pl, r) in
    match r, g with

    | Axiom, (gamma, f) when mem_alpha f gamma ->
        [], build_inference 0

    | Classical, (_, Or(Not f, g)) 
        when alpha_equivalent f g ->
        [], build_inference 0
    | Classical, (_, Or(f, Not g)) 
        when alpha_equivalent f g ->
        [], build_inference 0

    | Pierce, (_, Implies(Implies(Implies(f,_),h),k))
        when alpha_equivalent f h
            && alpha_equivalent f k ->
        [], build_inference 0

    | IntroImplies, (gamma, Implies(f1, f2)) ->
        [(f1::gamma, f2)], build_inference 1
    | ElimImplies hyp, (gamma, f) ->
        [ (gamma, Implies(hyp, f)); (gamma, hyp) ],
        build_inference 2

    | IntroAnd, (gamma, And(f1, f2)) ->
        [(gamma, f1); (gamma, f2)], 
        build_inference 2
    | ElimAnd(is_left,fnew), (gamma, f) ->
        [(gamma, if is_left then And(f,fnew) else And(fnew,f))], 
        build_inference 1

    | IntroOr is_left, (gamma, Or(f1, f2)) ->
        [(gamma, if is_left then f1 else f2)],
        build_inference 1
    | ElimOr (f1,f2), (gamma, f) ->
        [(gamma, Or(f1,f2)); (f1::gamma, f); (f2::gamma, f)],
        build_inference 3

    | IntroNot, (gamma, Not f) ->
        [(f :: gamma, Absurd)], build_inference 1
    | ElimNot f, (gamma, Absurd) ->
        [(gamma, f); (gamma, Not f)], build_inference 2

    | IntroForall x, (gamma, Forall(y, f)) ->
        [subst_sequent y (Var x) (gamma, f)], build_inference 1
    | ElimForall (x, t), (gamma, f) -> 
        [(gamma, Forall(x, rev_subst x t f))], build_inference 1

    | IntroExists t, (gamma, Exists(x, f)) ->
        [subst_sequent x t (gamma, f)], build_inference 1
    | ElimExists (x,f), (gamma, g) ->
        [ (gamma, Exists(x, f)); (f::gamma, g) ],
        build_inference 2

    | ElimAbsurd, (gamma, _) ->
        [(gamma, Absurd)], build_inference 1

    | _ -> raise InvalidRule

let rec split_at_nth l n =
    match l, n with
    | _, 0 -> [], l
    | [], _ -> failwith "Empty list"
    | t::q, _ ->
        let l1, l2 = split_at_nth q (n-1) in
        (t::l1, l2)

let apply_rule r c =
    let goals, proof_gen = c in
    match goals with
    | [] -> raise InvalidRule
    | g::goals' ->
        let new_goals, new_gen = apply_rule_to_goal r g in
        let n = List.length new_goals in
        new_goals @ goals', 
            (fun pl -> 
                let pl1, pl2 = split_at_nth pl n in
                proof_gen
                    ((new_gen pl1) :: pl2))

let detect_rule_sequent g =
    let _, f = g in
    match f with
    | And(_,_) -> Some IntroAnd
    | Implies(_,_) -> Some IntroImplies
    | Forall(x,_) -> Some (IntroForall x)
    | Not _ -> Some IntroNot
    | _ -> None

let detect_rule c =
    let goals, _ = c in
    match goals with
    | [] -> None
    | g::_ -> detect_rule_sequent g

