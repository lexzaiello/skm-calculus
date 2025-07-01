import SkLean.Ast2

namespace valid_judgment

lemma imp_m : valid_judgment e t → _root_.beta_eq (trivial_typing e) t := by
  intro h_t
  induction h_t
  repeat exact beta_eq.rfl
  case beta_eq t₁ t₂ e' h_t₁ h_t₂ ih =>
    apply beta_eq.symm
    apply beta_eq.trans
    exact (beta_eq.symm h_t₁)
    exact (beta_eq.symm ih)

theorem preservation_easy : valid_judgment e t → is_eval_once e e' → ∃ t', valid_judgment e' t' := by
  intro h_t h_eval
  induction h_t
  case k n =>
    use trivial_typing SKM[K n]
    cases h_eval
  case s n =>
    use trivial_typing SKM[S n]
    cases h_eval
  case m n =>
    use trivial_typing SKM[M n]
    cases h_eval
  case call_k x t_x n y h_t_x ih =>
    cases h_eval
    use t_x
    case left lhs' a =>
      cases a
      case left lhs' a =>
        cases a
  case call_s x z y t_call n h_t_call h_u ih =>
    cases h_eval
    use t_call
    case left lhs' a =>
      cases a
      case left lhs' a =>
        cases a
        case left lhs' a =>
          cases a
  case call_m e'' t' n h_t ih =>
    

end valid_judgment
