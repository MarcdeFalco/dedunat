open React
open Lwt
open LTerm_text
open Engine

let make_prompt env =
  let prompt =
    (match env.context with
    | None -> "Nothing to prove "
    | Some (goals, _) -> (
        match goals with
        | [] -> "No more goals to prove. Print/LaTeX or Qed "
        | g :: goals' ->
            String.concat ""
              (List.map
                 (fun g' ->
                   Printf.sprintf "Remaining Goal : %s\n"
                     (PrettyPrinting.string_of_sequent g'))
                 goals')
            ^ Printf.sprintf "Goal : %s " (PrettyPrinting.string_of_sequent g)))
    ^ "> "
  in
  eval [ S prompt ]

class read_line ~term ~history ~env =
  object (self)
    inherit LTerm_read_line.read_line ~history ()
    inherit [Zed_string.t] LTerm_read_line.term term
    method! show_box = false

    method! complete =
      if not (Config.is_ascii ()) then (
        let s = Zed_rope.to_string self#input_prev in
        let n = Zed_string.length s in

        let symbols =
          List.map Zed_char.of_utf8 [ "→"; "∧"; "∨"; "¬"; "⟂"; "∀"; "∃" ]
        in

        let rec index x l =
          match l with
          | [] -> raise Not_found
          | t :: _ when t = x -> 0
          | _ :: q -> 1 + index x q
        in

        let pop, next =
          if n = 0 || not (List.mem (Zed_string.get s (n - 1)) symbols) then
            (false, Zed_string.make 1 (List.hd symbols))
          else
            let c = Zed_string.get s (n - 1) in
            let i = index c symbols in
            let next =
              if i = List.length symbols - 1 then Zed_string.of_utf8 ""
              else Zed_string.make 1 (List.nth symbols (i + 1))
            in
            (true, next)
        in

        if pop then Zed_edit.delete_prev_char self#context;
        Zed_edit.insert self#context (Zed_rope.of_string next))

    initializer self#set_prompt (S.const (make_prompt env))
  end

let rec loop term history env =
  Lwt.catch
    (fun () ->
      let rl =
        new read_line ~term ~history:(LTerm_history.contents history) ~env
      in

      rl#run >|= fun command -> Some command)
    (function Sys.Break -> return None | exn -> Lwt.fail exn)
  >>= function
  | Some command ->
      let command_utf8 = Zed_string.to_utf8 command in
      let env, out =
        try eval_tactic env command_utf8
        with Quit ->
          Printf.printf "Quitting";
          raise LTerm_read_line.Interrupt
      in
      LTerm.fprintls term (eval [ S out ]) >>= fun () ->
      LTerm_history.add history command;
      loop term history env
  | None -> loop term history env

let main () =
  LTerm_inputrc.load () >>= fun () ->
  Lwt.catch
    (fun () ->
      Lazy.force LTerm.stdout >>= fun term ->
      loop term (LTerm_history.create []) initial_env)
    (function
      | LTerm_read_line.Interrupt -> Lwt.return () | exn -> Lwt.fail exn)

let usage_msg = "dedunat [-ascii]"
let speclist = [ ("-ascii", Arg.Set Config.ascii, "Ouput symbols in ascii") ]

let () =
  Arg.parse speclist (fun _ -> ()) usage_msg;
  let usage =
    if Config.is_ascii () then "Ascii symbols : -> /\\ \\/ ~ _|_ \\-/ -]\n"
    else "Use <Tab> to cycle between symbols → ∧ ∨ ¬ ⟂ ∀ ∃\n"
  in
  print_string usage;
  flush stdout;
  Lwt_main.run (main ())
