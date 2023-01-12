open React
open Lwt
open LTerm_text


type env = {
    previous_env : env;
    context: Deduction.context option
}

let help_elim op = 
    let open Formula in
    let sdash = if Config.is_ascii () then "|-" else "⊢" in
    let sop = string_of_operator op in
    match op with
    | OpAnd ->
        "elim " ^ sop ^ " left B : Gamma " ^ sdash ^ " A => Gamma " ^ sdash
        ^ " B" ^ sop ^ "A\n"
    | OpOr ->
        "elim " ^ sop ^ " A, B : Gamma " ^ sdash ^ " C => Gamma "
        ^ sdash ^ " A" ^ sop ^ "B ; Gamma,A " ^ sdash 
        ^ " C ; Gamma,B " ^ sdash ^ " C\n"
    | OpImplies ->
        "elim " ^ sop ^ " A : Gamma " ^ sdash ^ " B => Gamma "
        ^ sdash ^ " A" ^ sop ^ "B ; Gamma " ^ sdash ^ " A\n"
    | OpNot ->
        "elim " ^ sop ^ " A  Gamma " ^ sdash ^ 
        " " ^ (if Config.is_ascii () then "_|_" else "⟂")
        ^ " => Gamma " ^ sdash ^ " A ; Gamma "
        ^ sdash ^ " " ^ sop ^ "A\n"
    | _ -> "todo\n"

let help_intro op = 
    let open Formula in
    let sdash = if Config.is_ascii () then "|-" else "⊢" in
    let sop = string_of_operator op in
    match op with
    | OpAnd ->
        "intro " ^ sop ^ " : Gamma " ^ sdash ^ "A" ^ sop ^ "B => Gamma "
        ^ sdash ^ " A ; Gamma " ^ sdash ^ " B\n"
    | OpOr ->
        "intro " ^ sop ^ " left : Gamma " ^ sdash ^ "A" ^ sop ^ "B => Gamma "
        ^ sdash ^ "A\n"
        ^ "intro " ^ sop ^ " right : Gamma " ^ sdash ^ "A" ^ sop ^ "B => Gamma "
        ^ sdash ^ "B\n"
    | OpImplies ->
        "intro " ^ sop ^ " : Gamma " ^ sdash ^ "A" ^ sop ^ "B => Gamma,A "
        ^ sdash ^ " B\n"
    | OpNot ->
        "intro " ^ sop ^ " : Gamma " ^ sdash ^ " " ^ sop ^ "A => Gamma,A "
        ^ sdash ^ " " ^ (if Config.is_ascii () then "_|_" else "⟂")
        ^ "\n"
    | _ -> "todo\n"


let help op =
    help_intro op ^
    help_elim op

let help_intros =
    let open Formula in
    String.concat ""
        (List.map help_intro
        [OpAnd; OpOr; OpImplies; OpNot; OpForall; OpExists; OpAbsurd])

let help_elims =
    let open Formula in
    String.concat ""
        (List.map help_elim
        [OpAnd; OpOr; OpImplies; OpNot; OpForall; OpExists; OpAbsurd])


let example_context =
    let open Formula in
    let open Deduction in
    let a = PropVar "A" in let b = PropVar "B" in
    [([And(a,b)],b)], fun _ ->
        Inference( ([], Implies(And(a,b),And(b,a))),
         [Inference( ([And(a,b)], And(b,a)),
          [
              Inference( ([And(a,b)], b), [], Unfinished );
           Inference( ([And(a,b)], a),
            [Inference( ([And(a,b)],And(a,b)), [], Axiom )], ElimAnd(true,b))
          ], IntroAnd)
         ], IntroImplies)

let rec initial_env =
    {
        previous_env = initial_env;
        context = None
    }

exception Quit
exception InvalidRule

let make_prompt env =
    let prompt = (match env.context with
        | None -> "Nothing to prove "
        | Some (goals, _) ->
            match goals with
            | [] -> "No more goals to prove. Print/LaTeX or Qed "
            | g::goals' ->
                String.concat "" 
                    (List.map (fun g' ->
                        Printf.sprintf "Remaining Goal : %s\n"
                            (Deduction.string_of_sequent g')) goals')
                    ^ Printf.sprintf "Goal : %s "
                            (Deduction.string_of_sequent g))
        ^ "> "
    in eval [ S prompt ]

class read_line ~term ~history ~env = object(self)
  inherit LTerm_read_line.read_line ~history ()
  inherit [Zed_string.t] LTerm_read_line.term term

  method! show_box = false

  method! complete =
      if not (Config.is_ascii ())
      then begin
          let s = Zed_rope.to_string self#input_prev in
          let n = Zed_string.length s in

          let symbols = 
              List.map Zed_char.of_utf8
              [ "→";"∧";"∨";"¬";"⟂";"∀";"∃" ]  in

          let rec index x l =
              match l with
              | [] -> raise Not_found
              | t::_ when t = x -> 0
              | _::q -> 1 + index x q in

          let pop, next = 
              if n = 0 || not (List.mem (Zed_string.get s (n-1)) symbols)
              then false, Zed_string.make 1 (List.hd symbols)
              else begin
                  let c = Zed_string.get s (n-1) in
                  let i = index c symbols in
                  let next = 
                      if i = List.length symbols - 1 
                      then Zed_string.of_utf8 ""
                      else Zed_string.make 1 (List.nth symbols (i+1)) in
                  true, next
              end in

          if pop 
          then Zed_edit.delete_prev_char self#context;
          Zed_edit.insert self#context (Zed_rope.of_string next)
        end

  initializer
    self#set_prompt (S.const (make_prompt env))
end

let eval_tactic env s =
    try
        let out = ref "" in
        let tl = Parser.tokenize s in
        let c = Parser.parse_command tl in
        let env = match c, env.context with
            | Command.Quit, _ -> raise Quit
            | Command.ApplyRule _, None ->
                out := "Nothing is being proved.\n";
                env
            | Command.ApplyRule r, Some c ->
                { previous_env = env; 
                  context = Some (Deduction.apply_rule r c) }
            | Command.Auto, Some c ->
                (match Deduction.detect_rule c with
                | None -> 
                    out := "Can't find rule to apply.\n";
                    env
                | Some r ->
                    { previous_env = env; 
                      context = Some (Deduction.apply_rule r c) })
            | Command.Undo, _ ->
                env.previous_env
            | Command.Prove f, None ->
                {  previous_env = env; 
                   context = Some (Deduction.initial_context f) }
            | Command.Qed, Some ([],_) ->
                { previous_env = initial_env;
                  context = None }
            | Command.Print, Some c ->
                out := Deduction.string_of_proof
                    (Deduction.proof_of_context c);
                env
            | Command.LaTeX, Some c ->
                out := Deduction.latex_of_proof
                    (Deduction.proof_of_context c);
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
            | _ -> env
        in env, !out
    with
        | Parser.LexingError -> 
                env, "Error lexing formula\n"
        | Parser.ExtraTokenError s -> 
                env, "Extra tokens at end of command: " ^ s
        | Parser.ParsingError -> 
                env, "Error parsing formula\n"
        | Deduction.InvalidRule -> 
                env, "Rule can't be applied.\n"

let rec loop term history env =
   Lwt.catch (fun () ->
   let rl = new read_line 
        ~term 
        ~history:(LTerm_history.contents history) 
        ~env in

    rl#run >|= fun command -> Some command)
    (function
      | Sys.Break -> return None
      | exn -> Lwt.fail exn)
  >>= function
  | Some command ->
    let command_utf8 = Zed_string.to_utf8 command in
    let env, out = eval_tactic env command_utf8 in
    LTerm.fprintls term (eval [S out])
    >>= fun () ->
    LTerm_history.add history command;
    loop term history env
  | None ->
    loop term history env

let main () =
  LTerm_inputrc.load ()
  >>= fun () ->
  Lwt.catch (fun () ->
    Lazy.force LTerm.stdout
    >>= fun term ->
    loop term (LTerm_history.create []) initial_env)
    (function
      | LTerm_read_line.Interrupt -> Lwt.return ()
      | exn -> Lwt.fail exn)

let usage_msg = "dedunat [-ascii]"

let speclist =
    [( "-ascii", Arg.Set Config.ascii, "Ouput symbols in ascii")]

let () =
    Arg.parse speclist (fun _ -> ()) usage_msg;
    let usage = 
        if Config.is_ascii ()
        then "Ascii symbols : -> /\\ \\/ ~ _|_ \\-/ -]\n"
        else "Use <Tab> to cycle between symbols → ∧ ∨ ¬ ⟂ ∀ ∃\n" 
    in
    print_string usage;
    flush stdout;
    Lwt_main.run (main ())
