type command =
    | Quit
    | Prove of Formula.formula
    | ApplyRule of Deduction.rule
    | Undo
    | Print
    | Qed
