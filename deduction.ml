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
  | Peirce
  | Assume
  | Unfinished

type sequent = formula list * formula

let subst_sequent x t (fl, f) = (List.map (subst x t) fl, subst x t f)

let apply_def_sequent def (fl, f) =
  (List.map (apply_def def) fl, apply_def def f)

type proof = Inference of sequent * proof list * rule
type context = sequent list * (proof list -> proof)

exception InvalidRule
exception InvalidProof

let apply_defs_context defs c =
  let goals, proof_gen = c in
  match goals with
  | [] -> raise InvalidRule
  | g :: goals' ->
      ( List.fold_left (fun g def -> apply_def_sequent def g) g defs :: goals',
        proof_gen )

let unfinished_proof g = Inference (g, [], Unfinished)

let initial_context seq =
  ([ seq ], fun l -> match l with [ p ] -> p | _ -> failwith "Invalid proof")

let proof_of_context (gl, c) =
  let pl = List.map unfinished_proof gl in
  c pl

(* The prover is here. Everything is else is for handling input/output *)
let apply_rule_to_goal r g =
  let build_inference n pl =
    if List.length pl <> n then raise InvalidProof else Inference (g, pl, r)
  in
  match (r, g) with
  | Assume, _ -> ([], build_inference 0)
  | Axiom, (gamma, f) when mem_alpha f gamma -> ([], build_inference 0)
  | Classical, (_, Or (Not f, g)) when alpha_equivalent f g ->
      ([], build_inference 0)
  | Classical, (_, Or (f, Not g)) when alpha_equivalent f g ->
      ([], build_inference 0)
  | Peirce, (_, Implies (Implies (Implies (f, _), h), k))
    when alpha_equivalent f h && alpha_equivalent f k ->
      ([], build_inference 0)
  | IntroImplies, (gamma, Implies (f1, f2)) ->
      ([ (f1 :: gamma, f2) ], build_inference 1)
  | ElimImplies hyp, (gamma, f) ->
      ([ (gamma, Implies (hyp, f)); (gamma, hyp) ], build_inference 2)
  | IntroAnd, (gamma, And (f1, f2)) ->
      ([ (gamma, f1); (gamma, f2) ], build_inference 2)
  | ElimAnd (is_left, fnew), (gamma, f) ->
      ( [ (gamma, if is_left then And (f, fnew) else And (fnew, f)) ],
        build_inference 1 )
  | IntroOr is_left, (gamma, Or (f1, f2)) ->
      ([ (gamma, if is_left then f1 else f2) ], build_inference 1)
  | ElimOr (f1, f2), (gamma, f) ->
      ( [ (gamma, Or (f1, f2)); (f1 :: gamma, f); (f2 :: gamma, f) ],
        build_inference 3 )
  | IntroNot, (gamma, Not f) -> ([ (f :: gamma, Absurd) ], build_inference 1)
  | ElimNot f, (gamma, Absurd) ->
      ([ (gamma, f); (gamma, Not f) ], build_inference 2)
  | IntroForall x, (gamma, Forall (y, f)) ->
      ([ subst_sequent y (Var x) (gamma, f) ], build_inference 1)
  | ElimForall (x, t), (gamma, f) ->
      ([ (gamma, Forall (x, rev_subst x t f)) ], build_inference 1)
  | IntroExists t, (gamma, Exists (x, f)) ->
      ([ subst_sequent x t (gamma, f) ], build_inference 1)
  | ElimExists (x, f), (gamma, g) ->
      ([ (gamma, Exists (x, f)); (f :: gamma, g) ], build_inference 2)
  | ElimAbsurd, (gamma, _) -> ([ (gamma, Absurd) ], build_inference 1)
  | _ -> raise InvalidRule

let rec split_at_nth l n =
  match (l, n) with
  | _, 0 -> ([], l)
  | [], _ -> failwith "Empty list"
  | t :: q, _ ->
      let l1, l2 = split_at_nth q (n - 1) in
      (t :: l1, l2)

let apply_rule r c =
  let goals, proof_gen = c in
  match goals with
  | [] -> raise InvalidRule
  | g :: goals' ->
      let new_goals, new_gen = apply_rule_to_goal r g in
      let n = List.length new_goals in
      ( new_goals @ goals',
        fun pl ->
          let pl1, pl2 = split_at_nth pl n in
          proof_gen (new_gen pl1 :: pl2) )

let detect_rule_sequent g =
  let _, f = g in
  match f with
  | And (_, _) -> Some IntroAnd
  | Implies (_, _) -> Some IntroImplies
  | Forall (x, _) -> Some (IntroForall x)
  | Not _ -> Some IntroNot
  | _ -> None

let detect_rule c =
  let goals, _ = c in
  match goals with [] -> None | g :: _ -> detect_rule_sequent g
