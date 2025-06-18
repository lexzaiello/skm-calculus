import SkLean.Ast2

namespace valid_judgment

lemma eval_preserves_judgment_hard : ∀ e e' t, valid_judgment e t → is_eval_once e e' → valid_judgment e' t := by
  intro e e' t h_t h_eval
  induction h_t
  cases h_eval
  cases h_eval
  cases h_eval
  case call lhs rhs h_u h_t_lhs h_t_rhs ih₁ ih₂ =>
    cases h_eval
    cases h_t_lhs
    cases h_t_lhs
    cases h_t_lhs
    cases h_t_lhs
    cases h_t_lhs

end valid_judgment
