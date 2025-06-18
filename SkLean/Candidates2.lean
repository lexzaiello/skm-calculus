import SkLean.Ast2

/-
# Hierarchied SK Reducibility Candidates

-/

inductive is_candidate_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e')) → is_candidate_n 0 e e
  | succ  : is_eval_once e e'
    → e_final.max_universe < e.max_universe
    → is_candidate_n n e' e_final
    → is_candidate_n n.succ e e_final

namespace is_candidate_for

lemma imp_judgment : is_candidate_for e t → valid_judgment e t := by
  intro h_r
  induction h_r
  case stuck t' h_step h =>
    exact h
  case step e' t' h_beq h_u =>
    
    sorry

end is_candidate_for

