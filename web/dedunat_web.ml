(* Interface JavaScript de Dedunat : expose un objet global [dedunat]
   utilisé par index.html. *)

open Js_of_ocaml
open Deduction

let env = ref Engine.initial_env

let escape s =
  let b = Buffer.create (String.length s) in
  String.iter
    (function
      | '<' -> Buffer.add_string b "&lt;"
      | '>' -> Buffer.add_string b "&gt;"
      | '&' -> Buffer.add_string b "&amp;"
      | '"' -> Buffer.add_string b "&quot;"
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let html_of_sequent (gamma, f) =
  let hyps = String.concat ", " (List.map PrettyPrinting.string_of_formula gamma) in
  let sdash = if Config.is_ascii () then "|-" else "⊢" in
  (if hyps = "" then "" else "<span class=\"hyps\">" ^ escape hyps ^ "</span> ")
  ^ "<span class=\"dash\">" ^ escape sdash ^ "</span> "
  ^ "<span class=\"concl\">"
  ^ escape (PrettyPrinting.string_of_formula f)
  ^ "</span>"

(* Arbre de preuve en HTML : chaque nœud contient ses prémisses, une barre
   d'inférence étiquetée par la règle et le séquent conclusion. Le premier
   séquent non prouvé (dans l'ordre de parcours) est le but courant. *)
let html_of_proof p =
  let current = ref true in
  let b = Buffer.create 1024 in
  let rec aux (Inference (seq, pl, r)) =
    let cls =
      if r = Unfinished then
        if !current then (
          current := false;
          "node open current")
        else "node open"
      else "node"
    in
    Buffer.add_string b ("<div class=\"" ^ cls ^ "\">");
    if pl <> [] then (
      Buffer.add_string b "<div class=\"premises\">";
      List.iter aux pl;
      Buffer.add_string b "</div>");
    Buffer.add_string b "<div class=\"bar\">";
    if r <> Unfinished then
      Buffer.add_string b
        ("<span class=\"rule\">"
        ^ escape (PrettyPrinting.string_of_rule r)
        ^ "</span>");
    Buffer.add_string b "</div>";
    Buffer.add_string b
      ("<div class=\"sequent\">" ^ html_of_sequent seq ^ "</div></div>");
  in
  aux p;
  Buffer.contents b

let exec line =
  let line = Js.to_string line in
  let before = !env in
  let quit, out =
    try
      let e, out = Engine.eval_tactic !env line in
      env := e;
      (false, out)
    with Engine.Quit -> (true, "")
  in
  let finished =
    match (before.Engine.context, !env.Engine.context) with
    | Some ([], _), None -> true
    | _ -> false
  in
  object%js
    val output = Js.string out
    val quit = Js.bool quit
    val finished = Js.bool finished
  end

let goals () =
  match !env.Engine.context with
  | None -> Js.null
  | Some (gl, _) ->
      Js.some
        (Js.array
           (Array.of_list
              (List.map (fun g -> Js.string (html_of_sequent g)) gl)))

let proof () =
  match !env.Engine.context with
  | None -> Js.null
  | Some c -> Js.some (Js.string (html_of_proof (proof_of_context c)))

let reset () = env := Engine.initial_env

let () =
  Js.export "dedunat"
    object%js
      method exec line = exec line
      method goals = goals ()
      method proof = proof ()
      method reset = reset ()
      method setAscii b = Config.ascii := Js.to_bool b
      method isAscii = Js.bool (Config.is_ascii ())
    end
