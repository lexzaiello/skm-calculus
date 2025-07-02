import SkLean.Ast2

namespace valid_judgment

lemma imp_exists_eval : valid_judgment e t → ∃ e', is_eval_once (trivial_typing e) e' := by
  intro h_t
  induction e
  case m n =>
    use SKM[(M n.succ)]
    apply is_eval_once.m_m
  case k n =>
    use SKM[(K n.succ)]
    apply is_eval_once.m_k
  case s n =>
    use SKM[(S n.succ)]
    apply is_eval_once.m_s
  case call lhs rhs ih₁ ih₂ =>
    use SKM[(#(trivial_typing lhs) #(trivial_typing rhs))]
    apply is_eval_once.m_call

lemma call_exists_lhs_rhs_t : valid_judgment SKM[(lhs rhs)] t → ∃ t_lhs t_rhs, valid_judgment lhs t_lhs ∧ valid_judgment rhs t_rhs := by
  intro h_t
  cases h_t
  case call_k x t_x t_y n h_t_x h_t_y =>
    use (trivial_typing SKM[((K n) x)])
    use t_y
    exact ⟨valid_judgment.call_k₁ h_t_x, h_t_y⟩
  case call_k₁ t_x n h_t_x =>
    use (trivial_typing SKM[(K n)])
    use t_x
    exact ⟨by apply valid_judgment.k, h_t_x⟩
  case call_s₁ t_x n h_t_x =>
    use (trivial_typing SKM[(S n)])
    use t_x
    exact ⟨by apply valid_judgment.s, h_t_x⟩
  case call_s₂ x t_x t_y n h_t_x h_t_y =>
    use (trivial_typing SKM[((S n) x)])
    use t_y
    exact ⟨valid_judgment.call_s₁ h_t_x, h_t_y⟩
  case call_s x y z t_x t_y t_call n h_t_x h_t_y h_t_z h_t_call h_u =>
    use trivial_typing SKM[(((S n) x) y)]
    simp_all
    constructor
    apply valid_judgment.call_s₂
    exact h_t_x
    exact h_t_y
    use t_call
  case call_m t n h_t =>
    use (trivial_typing SKM[(M n)])
    use t
    exact ⟨valid_judgment.m n, h_t⟩
  case call t_lhs t_rhs e' h_t_lhs h_t_rhs h_eval h_u =>
    use t_lhs
    use t_rhs

lemma imp_m : valid_judgment e t → _root_.beta_eq (trivial_typing e) t := by
  intro h_t
  induction h_t
  repeat exact beta_eq.rfl

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
  case call_k₁ x t_x n h_t_x ih =>
    cases h_eval
    case left h =>
      cases h
  case call_s₁ x t_x n h_t_x ih =>
    cases h_eval
    case left h =>
      cases h
  case call_s₂ x t_x y t_y n h_t_x h_t_y ih₁ ih₂ =>
    cases h_eval
    case left h =>
      cases h
      case left h =>
        cases h
  case call_k x t_x y t_y n h_t_x h_t_y ih₁ ih₂ =>
    cases h_eval
    use t_x
    case left h =>
      cases h
      case left h =>
        cases h
  case call_s x z y t_call t_x t_y t_z n h_t_call h_t_x h_t_y h_t_z h_u ih₁ ih₂ ih₃ ih₄ =>
    cases h_eval
    use t_call
    case left h =>
      cases h
      case left h =>
        cases h
        case left h =>
          cases h
  case call_m e t n h_t h_eval₂ =>
    cases h_eval
    case m_k n =>
      use trivial_typing SKM[(K n.succ)]
      apply valid_judgment.k
    case m_s n =>
      use trivial_typing SKM[(S n.succ)]
      apply valid_judgment.s
    case m_m n =>
      use trivial_typing SKM[(M n.succ)]
      apply valid_judgment.m
    case m_call t' lhs rhs =>
      use trivial_typing SKM[(#(trivial_typing lhs) #(trivial_typing rhs))]
      have ⟨t_lhs, t_rhs, h_t_lhs, h_t_rhs⟩ := h_t.call_exists_lhs_rhs_t
      apply valid_judgment.call
      apply valid_judgment.call_m
      exact h_t_lhs
      apply valid_judgment.call_m
      exact h_t_rhs
      apply is_eval_once.left
      
      sorry
    sorry

end valid_judgment
