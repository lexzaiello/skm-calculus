import SkLean.Ast3
import SkLean.Checker
import SkLean.Eval

namespace Expr

theorem preservation (h_t : infer e = t) (h_eval : eval_once e = .some e') : infer e' = t := by
  induction e
  repeat (unfold eval_once at h_eval; simp_all)
  case call lhs rhs ih₁ ih₂ =>
    
    sorry

end Expr
