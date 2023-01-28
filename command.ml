type command =
  | Quit
  | Define of Formula.definition
  | Unroll
  | Prove of Deduction.sequent
  | ApplyRule of Deduction.rule
  | HelpOp of Formula.operator
  | HelpElim
  | HelpIntro
  | Help
  | Undo
  | Auto
  | Print
  | French
  | LaTeX
  | Qed
