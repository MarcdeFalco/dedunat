type env = {
  previous_env : env;
  definitions : Formula.definition list;
  context : Deduction.context option;
}

let help_elim op =
  let open Formula in
  let sdash = if Config.is_ascii () then "|-" else "⊢" in
  let sop = PrettyPrinting.string_of_operator op in
  match op with
  | OpAnd ->
      "elim " ^ sop ^ " left B : Gamma " ^ sdash ^ " A => Gamma " ^ sdash ^ " B"
      ^ sop ^ "A\n"
  | OpOr ->
      "elim " ^ sop ^ " A, B : Gamma " ^ sdash ^ " C => Gamma " ^ sdash ^ " A"
      ^ sop ^ "B ; Gamma,A " ^ sdash ^ " C ; Gamma,B " ^ sdash ^ " C\n"
  | OpImplies ->
      "elim " ^ sop ^ " A : Gamma " ^ sdash ^ " B => Gamma " ^ sdash ^ " A"
      ^ sop ^ "B ; Gamma " ^ sdash ^ " A\n"
  | OpNot ->
      "elim " ^ sop ^ " A  Gamma " ^ sdash ^ " "
      ^ (if Config.is_ascii () then "_|_" else "⟂")
      ^ " => Gamma " ^ sdash ^ " A ; Gamma " ^ sdash ^ " " ^ sop ^ "A\n"
  | OpAbsurd ->
      "elim " ^ sop ^ " : Gamma " ^ sdash ^ " A => Gamma " ^ sdash ^ " " ^ sop
      ^ "\n"
  | OpForall ->
      "elim " ^ sop ^ " x t : " ^ "Gamma " ^ sdash ^ " A[x\\t]" ^ " => Gamma "
      ^ sdash ^ sop ^ "x.A\n"
  | OpExists ->
      "elim " ^ sop ^ " x A : " ^ "Gamma " ^ sdash ^ " B => Gamma " ^ sdash
      ^ " " ^ sop ^ "x.A ; Gamma,A " ^ sdash ^ " B\n"

let help_intro op =
  let open Formula in
  let sdash = if Config.is_ascii () then "|-" else "⊢" in
  let sop = PrettyPrinting.string_of_operator op in
  match op with
  | OpAnd ->
      "intro " ^ sop ^ " : Gamma " ^ sdash ^ "A" ^ sop ^ "B => Gamma " ^ sdash
      ^ " A ; Gamma " ^ sdash ^ " B\n"
  | OpOr ->
      "intro " ^ sop ^ " left : Gamma " ^ sdash ^ "A" ^ sop ^ "B => Gamma "
      ^ sdash ^ "A\n" ^ "intro " ^ sop ^ " right : Gamma " ^ sdash ^ "A" ^ sop
      ^ "B => Gamma " ^ sdash ^ "B\n"
  | OpImplies ->
      "intro " ^ sop ^ " : Gamma " ^ sdash ^ "A" ^ sop ^ "B => Gamma,A " ^ sdash
      ^ " B\n"
  | OpNot ->
      "intro " ^ sop ^ " : Gamma " ^ sdash ^ " " ^ sop ^ "A => Gamma,A " ^ sdash
      ^ " "
      ^ (if Config.is_ascii () then "_|_" else "⟂")
      ^ "\n"
  | OpAbsurd -> ""
  | OpForall ->
      "intro " ^ sop ^ " ident : Gamma " ^ sdash ^ " " ^ sop ^ "x.A => Gamma "
      ^ sdash ^ "A[x\\ident]\n"
  | OpExists ->
      "intro " ^ sop ^ " t : Gamma " ^ sdash ^ " " ^ sop ^ "x.A => Gamma "
      ^ sdash ^ "A[x\\t]\n"

let help op = help_intro op ^ help_elim op

let help_intros =
  let open Formula in
  String.concat ""
    (List.map help_intro [ OpAnd; OpOr; OpImplies; OpNot; OpForall; OpExists ])

let help_elims =
  let open Formula in
  String.concat ""
    (List.map help_elim
       [ OpAnd; OpOr; OpImplies; OpNot; OpForall; OpExists; OpAbsurd ])

let rec initial_env =
  { previous_env = initial_env; definitions = []; context = None }

exception Quit

let eval_tactic env s =
  try
    let out = ref "" in
    let tl = Parser.tokenize s in
    let c = Parser.parse_command tl in
    let env =
      match (c, env.context) with
      | Command.ApplyRule _, None ->
          out := "Nothing is being proved.\n";
          env
      | Command.ApplyRule r, Some c ->
          {
            previous_env = env;
            definitions = env.definitions;
            context = Some (Deduction.apply_rule r c);
          }
      | Command.Auto, Some c -> (
          match Deduction.detect_rule c with
          | None ->
              out := "Can't find rule to apply.\n";
              env
          | Some r ->
              {
                previous_env = env;
                definitions = env.definitions;
                context = Some (Deduction.apply_rule r c);
              })
      | Command.Undo, _ -> env.previous_env
      | Command.Prove seq, None ->
          {
            previous_env = env;
            definitions = env.definitions;
            context = Some (Deduction.initial_context seq);
          }
      | Command.Qed, Some ([], _) ->
          { previous_env = env; definitions = env.definitions; context = None }
      | Command.Print, Some c ->
          out := PrettyPrinting.string_of_proof (Deduction.proof_of_context c);
          env
      | Command.LaTeX, Some c ->
          out := PrettyPrinting.latex_of_proof (Deduction.proof_of_context c);
          env
      | Command.French, Some c ->
          out :=
            PrettyPrinting.frenchmath_of_proof (Deduction.proof_of_context c);
          env
      | Command.HelpOp op, _ ->
          out := help op;
          env
      | Command.HelpIntro, _ ->
          out := help_intros;
          env
      | Command.HelpElim, _ ->
          out := help_elims;
          env
      | Command.Help, _ ->
          out := help_intros ^ help_elims;
          env
      | Command.Quit, _ -> raise Quit
      | Command.Unroll, Some c ->
          {
            env with
            previous_env = env;
            context = Some (Deduction.apply_defs_context env.definitions c);
          }
      | Command.Define def, _ ->
          { env with previous_env = env; definitions = def :: env.definitions }
      | _ -> env
    in
    (env, !out)
  with
  | Parser.LexingError -> (env, "Error lexing formula\n")
  | Parser.ExtraTokenError s -> (env, "Extra tokens at end of command: " ^ s)
  | Parser.ParsingError -> (env, "Error parsing formula\n")
  | Deduction.InvalidRule -> (env, "Rule can't be applied.\n")
