type token = 
    | Ident of string
    | Keyword of string
    | Num of int
    | Dot | Comma 
    | LPar | RPar 
    | TOr | TAnd | TNot | TImplies
    | TForall | TExists | TAbsurd
    | TEntails

let string_of_token tok = match tok with
    | Ident x -> x
    | Keyword x -> x
    | Num n -> string_of_int n
    | Dot -> "."
    | Comma -> ","
    | LPar -> "("
    | RPar -> ")"
    | TOr -> "\\/"
    | TAnd -> "/\\"
    | TImplies -> "->"
    | TNot -> "~"
    | TForall -> "\\-/"
    | TExists -> "-]"
    | TAbsurd -> "_|_"
    | TEntails -> "|-"

let keywords = [
    "print"; "intro"; "elim";"auto";
    "classical";"peirce"; "help";
    "left"; "right"; "qed"; "prove";
    "latex"; "quit"; "undo"; "axiom"
]

exception LexingError

let is_alpha c =
    let n  = Char.code c in
    (Char.code 'a' <= n && n <= Char.code 'z')
    ||  (Char.code 'A' <= n && n <= Char.code 'Z')

let is_digit c =
    let n  = Char.code c in
    (Char.code '0' <= n && n <= Char.code '9')

let rec extract_num s =
    match s with
    | c::q when is_digit c ->
        let i, s' = extract_num q in
        (c::i, s')
    | _ -> [], s

let extract_ident s =
    let rec extract_aux s =
        match s with
        | c::q when is_digit c || is_alpha c || c = '_' ->
            let i, s' = extract_aux q in
            (c::i, s')
        | _ -> [], s
    in
    match s with
    | c::_ when is_alpha c ->
        extract_aux s
    | _ -> [], s

let rec lexer s =
    match s with
    | [] -> []
    | ' '::q -> lexer q (* ignore space *)
    | ','::q -> Comma :: lexer q
    | '.'::q -> Dot :: lexer q
    | '('::q -> LPar :: lexer q
    | ')'::q -> RPar :: lexer q
    | '|'::'-'::q | '\\' :: 'v' :: 'd' :: 'a' :: 's' :: 'h' :: q 
        -> TEntails :: lexer q
    | '\\'::'/'::q | '\\' :: 'l' :: 'o' :: 'r' :: q | '\226' :: '\136' :: '\168' :: q -> TOr :: lexer q
    | '/'::'\\'::q | '\\' :: 'l' :: 'a' :: 'n' :: 'd' :: q |  '\226' :: '\136' :: '\167' :: q -> TAnd :: lexer q
    | '-'::'>'::q | '\\' :: 't' :: 'o' :: q | '\226' :: '\134' :: '\146' :: q -> TImplies :: lexer q
    | '~'::q | '\\' :: 'n' :: 'e' :: 'g' :: q | '\194' :: '\172' :: q -> TNot :: lexer q
    | '\\'::'-'::'/'::q | '\\' :: 'f' :: 'o' :: 'r' :: 'a':: 'l' :: 'l' :: q | '\226' :: '\136' :: '\128' :: q -> TForall :: lexer q
    | '-'::']'::q | '\\' :: 'e' :: 'x' :: 'i' :: 's' :: 't' :: 's' :: q | '\226' :: '\136' :: '\131' :: q -> TExists :: lexer q
    | '_' :: '|' :: '_' :: q | '\\' :: 'b' :: 'o' :: 't' :: q | '\226' :: '\159' :: '\130' :: q -> TAbsurd :: lexer q
    | x :: _ when is_digit x ->
        let x, q = extract_num s in
        if x = []
        then raise LexingError
        else Num (int_of_string 
                (String.concat "" (List.map (String.make 1) x)))
            :: lexer q
    | _ ->
        let x, q = extract_ident s in
        if x = []
        then raise LexingError
        else let x = String.concat "" (List.map (String.make 1) x) in
            let xl = String.lowercase_ascii x in
            (if List.mem xl keywords then Keyword xl else Ident x)
            :: lexer q

let tokenize s =
    lexer (List.of_seq (String.to_seq s))

exception ParsingError
exception ExtraTokenError of string

let rec parse_term_list tl =
    match tl with
    | [] -> raise ParsingError
    | RPar :: _ -> [], tl
    | _ -> let t, tl' = parse_term tl in
        match tl' with
        | RPar :: _ -> [t], tl'
        | Comma :: tl'' -> 
            let term_l, tl''' = parse_term_list tl'' in
            t::term_l, tl'''
        | _ -> raise ParsingError
and parse_term tl =
    match tl with
    | Ident x :: LPar :: q -> 
            let term_list, tl' = parse_term_list q in
                Formula.Function(x, term_list), tl'
    | Ident x :: q -> Formula.Var x, q
    | _ -> raise ParsingError

(*
grammar :
    formula2 := ~formula2 | (formula) | R(t1,..,tn) |  _|_ | A
        | \-/x.formula | -]x.formula
    formula1 := formula2 \/ formula1 | formula2 /\ formula1 | formula2
    formula := formula1 -> formula | formula1
*)

let rec parse_formula2 tl =
    match tl with
    | [] -> raise ParsingError
    | LPar :: q ->
            let f, tl' = parse_formula q in
            begin
                match tl' with
                | RPar :: q' ->
                    f, q'
                | _ -> raise ParsingError
            end
    | TNot :: tl' ->
            let f, tl'' = parse_formula2 tl' in
            Formula.Not f, tl''
    | Ident x :: LPar :: q ->
            let term_list, tl' = parse_term_list q in
            begin
                match tl' with
                | RPar :: q' ->
                    Formula.Rel(x, term_list), q'
                | _ -> raise ParsingError
            end
    | Ident x :: tl' -> PropVar x, tl'
    | TForall :: Ident x :: Dot :: q ->
            let f, tl' = parse_formula q in
            Formula.Forall(x, f), tl'
    | TExists :: Ident x :: Dot :: q ->
            let f, tl' = parse_formula q in
            Formula.Exists(x, f), tl'
    | TAbsurd :: q -> Formula.Absurd, q
    | _ -> raise ParsingError

and parse_formula1 tl =
    let f1, tl' = parse_formula2 tl in
    match tl' with
    | TOr :: q ->
            let f2, q' = parse_formula1 q in
            Formula.Or(f1,f2), q'
    | TAnd :: q ->
            let f2, q' = parse_formula1 q in
            Formula.And(f1,f2), q'
    | _ -> f1, tl'

and parse_formula tl =
    let f1, tl' = parse_formula1 tl in
    match tl' with
    | TImplies :: q ->
            let f2, q' = parse_formula q in
            Formula.Implies(f1,f2), q'
    | _ -> f1, tl'

let rec parse_sequent tl =
    let f, q = parse_formula tl in
    match q with
    | Comma::q ->
        let (l,f'), q = parse_sequent q in
        (f::l,f'), q
    | TEntails::q ->
        let f', q = parse_formula q in
        ([f],f'), q
    | _ -> ([],f),q

let parse_command tl =
    let c, remaining = match tl with
    | Keyword "quit" :: q -> Command.Quit, q
    | Keyword "french" :: q -> Command.French, q
    | Keyword "print" :: q -> Command.Print, q
    | Keyword "latex" :: q -> Command.LaTeX, q
    | Keyword "undo" :: q -> Command.Undo, q
    | Keyword "help" :: TAnd :: q -> Command.HelpOp Formula.OpAnd, q
    | Keyword "help" :: TOr :: q -> Command.HelpOp Formula.OpOr, q
    | Keyword "help" :: TNot :: q -> Command.HelpOp Formula.OpNot, q
    | Keyword "help" :: TImplies :: q -> Command.HelpOp Formula.OpImplies, q
    | Keyword "help" :: TForall :: q -> Command.HelpOp Formula.OpForall, q
    | Keyword "help" :: TExists :: q -> Command.HelpOp Formula.OpExists, q
    | Keyword "help" :: TAbsurd :: q -> Command.HelpOp Formula.OpAbsurd, q
    | Keyword "help" :: Keyword "elim" :: q -> Command.HelpElim, q
    | Keyword "help" :: Keyword "intro" :: q -> Command.HelpIntro, q
    | Keyword "help" :: q -> Command.Help, q
    | Keyword "axiom" :: q -> Command.ApplyRule Deduction.Axiom, q
    
    | Keyword "intro" :: TImplies :: q -> 
        Command.ApplyRule Deduction.IntroImplies, q
    | Keyword "elim" :: TImplies :: q -> 
        let f, q = parse_formula q in
        Command.ApplyRule (Deduction.ElimImplies f), q

    | Keyword "intro" :: TOr :: Keyword "left" :: q -> 
        Command.ApplyRule (Deduction.IntroOr true), q
    | Keyword "intro" :: TOr :: Keyword "right" :: q -> 
        Command.ApplyRule (Deduction.IntroOr false), q
    | Keyword "elim" :: TOr :: q -> 
        let f1, q = parse_formula q in
        (match q with
        | Comma :: q ->
            let f2, q = parse_formula q in
            Command.ApplyRule (Deduction.ElimOr (f1, f2)), q
        | _ -> raise ParsingError)

    | Keyword "intro" :: TAnd :: q -> 
        Command.ApplyRule Deduction.IntroAnd, q
    | Keyword "elim" :: TAnd :: Keyword "left" :: q -> 
        let f, q = parse_formula q in
        Command.ApplyRule (Deduction.ElimAnd (true, f)), q
    | Keyword "elim" :: TAnd :: Keyword "right" :: q -> 
        let f, q = parse_formula q in
        Command.ApplyRule (Deduction.ElimAnd (false, f)), q

    | Keyword "intro" :: TNot :: q ->
        Command.ApplyRule Deduction.IntroNot, q
    | Keyword "elim" :: TNot :: q ->
        let f, q = parse_formula q in
        Command.ApplyRule (Deduction.ElimNot f), q

    | Keyword "intro" :: TForall :: Ident x :: q ->
        Command.ApplyRule (Deduction.IntroForall x), q
    | Keyword "elim" :: TForall :: Ident x :: q ->
        let t, q = parse_term q in
        Command.ApplyRule (Deduction.ElimForall (x, t)), q
    | Keyword "intro" :: TExists :: q ->
        let t, q = parse_term q in
        Command.ApplyRule (Deduction.IntroExists t), q
    | Keyword "elim" :: TExists :: Ident x :: q ->
        let f, q = parse_formula q in
        Command.ApplyRule (Deduction.ElimExists (x, f)), q

    | Keyword "elim" :: TAbsurd :: q ->
        Command.ApplyRule Deduction.ElimAbsurd, q

    | Keyword "prove" :: q -> 
        let seq, q = parse_sequent q in

        Command.Prove seq, q

    | Keyword "classical" :: q -> 
        Command.ApplyRule Deduction.Classical, q
    | Keyword "peirce" :: q -> 
        Command.ApplyRule Deduction.Peirce, q

    | Keyword "auto" :: q -> 
        Command.Auto, q

    | Keyword "qed" :: q -> Command.Qed, q

    | _ -> raise ParsingError
    in if remaining <> [] 
       then 
           raise (ExtraTokenError
                (String.concat ";" (List.map string_of_token remaining)))
       else c


