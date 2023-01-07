open React
open Lwt
open LTerm_text


type env = {
    previous_env : env;
    context: Deduction.context option
}

let example_context =
    let open Formula in
    let open Deduction in
    let a = PropVar "A" in let b = PropVar "B" in
    [], fun _ ->
Inference( ([], Implies(And(a,b),And(b,a))),
 [Inference( ([And(a,b)], And(b,a)),
  [
   Inference( ([And(a,b)], b),
    [Inference( ([And(a,b)],And(a,b)), [], Axiom )], ElimAnd(false,a));
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
        | None -> "Nothing to prove.\n"
        | Some (goals, _) ->
            match goals with
            | [] -> "No more goals to prove. Print/LaTeX or Qed.\n"
            | g::goals' ->
                String.concat "" 
                    (List.map (fun g' ->
                        Printf.sprintf "Remaining Goal : %s\n"
                            (Deduction.string_of_sequent g')) goals')
                    ^ Printf.sprintf "Goal : %s\n"
                            (Deduction.string_of_sequent g))
        ^ "> "
    in eval [ S prompt ]

class read_line ~term ~history ~env = object(self)
  inherit LTerm_read_line.read_line ~history ()
  inherit [Zed_string.t] LTerm_read_line.term term

  method! show_box = false

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
    Lwt_main.run (main ())
