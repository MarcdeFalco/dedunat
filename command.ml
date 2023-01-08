type command =
    | Quit
    | Prove of Formula.formula
    | ApplyRule of Deduction.rule
    | Undo
    | Auto
    | Print
    | LaTeX
    | Qed
