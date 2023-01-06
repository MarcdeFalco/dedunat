open Formula

type rule =
    | ElimOr of formula * formula
    | ElimImplies of formula
    | ElimAnd of bool * formula
    | ElimNot of formula
    | ElimAbsurd

    | IntroImplies
    | IntroOr of bool
    | IntroAnd
    | IntroNot

    | Axiom

    | Unfinished

type sequent = formula list * formula

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

        | ElimAbsurd -> "\\perp_e"

        | Axiom -> "ax"

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

let string_of_sequent (fl, f) =
    String.concat ", " (List.map string_of_formula fl)
        ^ " |- " ^ string_of_formula f

exception InvalidRule
exception InvalidProof

let apply_rule_to_goal r g =
    let build_inference n pl =
        if List.length pl <> n
        then raise InvalidProof
        else Inference(g, pl, r) in
    match r, g with

    | Axiom, (gamma, f) when List.mem f gamma ->
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

