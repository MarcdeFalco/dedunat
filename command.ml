type command =
    | Quit
    | Prove of Formula.formula
    | ApplyRule of Deduction.rule
    | HelpOp of Formula.operator
    | HelpElim
    | HelpIntro
    | Help
    | Undo
    | Auto
    | Print
    | LaTeX
    | Qed
