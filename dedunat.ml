open React
open Lwt
open LTerm_text


type env = {
    previous_env : env;
    context: Deduction.context option
}

let rec initial_env =
    {
        previous_env = initial_env;
        context = None
    }

let print_env env =
    match env.context with
    | None -> Printf.printf "Nothing to prove.\n"
    | Some (goals, _) ->
        match goals with
        | [] -> Printf.printf "No more goals to prove. Print or Qed.\n"
        | g::goals' ->
            List.iter (fun g' ->
                Printf.printf "Remaining Goal : %s\n"
                    (Deduction.string_of_sequent g')) goals';
            Printf.printf "Goal : %s\n"
                (Deduction.string_of_sequent g)

exception Quit
exception InvalidRule

let make_prompt env =
    let prompt = (match env.context with
        | None -> "Nothing to prove.\n"
        | Some (goals, _) ->
            match goals with
            | [] -> "No more goals to prove. Print or Qed.\n"
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
        let c, _ = Parser.parse_command tl in
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
                out := Deduction.latex_of_proof
                    (Deduction.proof_of_context c);
                env
            | _ -> env
        in env, !out
    with
        | Parser.LexingError -> 
                env, "Error lexing formula\n"
        | Parser.ParsingError -> 
                env, "Error parsing formula\n"
        | Deduction.InvalidRule -> 
                env, "Rule can't be applied.\n"

(*
let rec command_loop term history env =
    print_env env;
    print_string "> ";
    try
        let tl = Parser.tokenize s in
        let c, _ = Parser.parse_command tl in
        let env' = match c, env.context with
            | Command.Quit, _ -> raise Quit
            | Command.ApplyRule _, None ->
                Printf.printf "Nothing is being proved.\n"; env
            | Command.ApplyRule r, Some c ->
                { previous_env = env; 
                  context = Some (Deduction.apply_rule r c) }
            | Command.Rollback, _ ->
                env.previous_env
            | Command.Prove f, None ->
                {  previous_env = env; 
                   context = Some (Deduction.initial_context f) }
            | Command.Qed, Some ([],_) ->
                { previous_env = initial_env;
                  context = None }
            | _ -> env
        in
        command_loop term history env'
    with 
    | Parser.LexingError -> 
            Printf.printf "Error lexing formula\n"; 
            command_loop term history env
    | Parser.ParsingError -> 
            Printf.printf "Error parsing formula\n"; 
            command_loop term history env
    | Deduction.InvalidRule -> 
            Printf.printf "Rule can't be applied.\n"; 
            command_loop term history env
    | Quit -> Printf.printf "Bye\n"

*)

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


let () =
    Lwt_main.run (main ())
