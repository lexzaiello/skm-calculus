import SkLean.Ast3
import SkLean.EvalTactic

example : beta_eq SKM[((K x) y)] x := by
  eval_to x
  
