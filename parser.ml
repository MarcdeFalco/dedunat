type tokens = 
    | Ident of string
    | Keyword of string
    | Num of int
    | Dot | Comma 
    | LPar | RPar 
    | TOr | TAnd | TNot | TImplies
    | TForall | TExists | TAbsurd

let keywords = [
    "print"; "intro"; "elim";
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
    | '\\'::'/'::q -> TOr :: lexer q
    | '/'::'\\'::q -> TAnd :: lexer q
    | '-'::'>'::q -> TImplies :: lexer q
    | '~'::q -> TNot :: lexer q
    | '\\'::'-'::'/'::q -> TForall :: lexer q
    | '-'::')'::q -> TExists :: lexer q
    | '_' :: '|' :: '_' :: q -> TAbsurd :: lexer q
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
        | \-/x.formula | -)x.formula
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
                Formula.Rel(x, term_list), tl'
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

let parse_command tl =
    match tl with
    | Keyword "quit" :: q -> Command.Quit, q
    | Keyword "print" :: q -> Command.Print, q
    | Keyword "undo" :: q -> Command.Undo, q
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

    | Keyword "elim" :: TAbsurd :: q ->
        Command.ApplyRule Deduction.ElimAbsurd, q

    | Keyword "prove" :: q -> 
        let f, q = parse_formula q in
        Command.Prove f, q

    | Keyword "qed" :: q -> Command.Qed, q

    | _ -> raise ParsingError


