import SkLean.Ast3
import SkLean.Eval

inductive IsComb : Ast.Expr → Prop
  | k   : IsComb SKM[K]
  | s   : IsComb SKM[S]
  | m   : IsComb SKM[M]
  | arr : IsComb SKM[#~>]

namespace IsComb

@[simp]
lemma no_step (h : IsComb e) : ¬ ∃ e', Expr.eval_once e = .some e' := by
  cases h
  repeat (intro ⟨e', h⟩; cases h)

end IsComb

inductive AllM : Ast.Expr → Prop
  | m    : AllM SKM[M]
  | m_m  : AllM SKM[(M M)]
  | call : AllM lhs
    → AllM SKM[(lhs M)]

namespace AllM

lemma no_step (h : AllM e) : ¬ ∃ e', IsEvalOnce e e' := by
  induction h
  intro ⟨e', h⟩
  cases h
  intro ⟨e', h⟩
  cases h
  repeat contradiction
  intro ⟨e', h⟩
  cases h
  repeat contradiction
  simp_all

end AllM

inductive IsValue : Ast.Expr → Prop
  | comb   : IsComb e
    → IsValue e
  | k₁     : IsValue SKM[(K α)]
  | k₂     : IsValue SKM[((K α) β)]
  | k₃     : IsValue SKM[(((K α) β) x)]
  | s₁     : IsValue SKM[(S α)]
  | s₂     : IsValue SKM[((S α) β)]
  | s₃     : IsValue SKM[(((S α) β) γ)]
  | s₄     : IsValue SKM[((((S α) β) γ) x)]
  | s₅     : IsValue SKM[(((((S α) β) γ) x) y)]
  | arr₁   : IsValue SKM[(#~> _α)]
  | arr    : IsValue SKM[(t_in ~> t_out)]
  | m_arr₁ : AllM m_e
    → IsValue SKM[((m_e #~>) t_in)]
  | m_arr  : AllM m_e
    → IsValue SKM[(((m_e #~>) t_in) t_out)]
  | m_k₁   : AllM m_e
    → IsValue SKM[((m_e K) α)]
  | m_s₁   : AllM m_e
    → IsValue SKM[((m_e S) α)]
  | m_s₂   : AllM m_e
    → IsValue SKM[(((m_e S) α) β)]
  | m_comb : IsComb e
    → AllM m_e
    → IsValue SKM[(m_e e)]

inductive IsValueNoArgStep : Ast.Expr → Prop
  | k    : IsValueNoArgStep SKM[K]
  | s    : IsValueNoArgStep SKM[S]
  | arr  : IsValueNoArgStep SKM[#~>]
  | s₁   : IsValueNoArgStep SKM[(S α)]
  | arr₁ : IsValueNoArgStep SKM[(#~> _α)]
  | m_k  : AllM m_e
    → IsValueNoArgStep SKM[(m_e K)]
  | m_s₁ : AllM m_e
    → IsValueNoArgStep SKM[((m_e S) α)]
  | m_s  : AllM m_e
    → IsValueNoArgStep SKM[(m_e S)]

inductive IsValueN : ℕ → Expr → Expr → Prop
  | val  : IsValue e → IsValueN 0 e e
  | succ : IsEvalOnce e e'
    → IsValueN n e' e_final
    → IsValueN n.succ e e_final

inductive HasType : Ast.Expr → Ast.Expr → Prop
  | comb  : IsComb e
    → HasType e SKM[(M e)]
  | k     : HasType α t_α
    → HasType β t_β
    → HasType SKM[((K α) β)] SKM[α !~> β !~> α]
  | s     : HasType α t_α
    → HasType β t_β
    → HasType γ t_γ
    → HasType SKM[(((S α) β) γ)] (Ast.Expr.mk_s_type t_α α β γ)
  | m_m   : IsComb e
    → HasType SKM[(M e)] SKM[((M M) e)]
  | arr   : HasType SKM[t_in ~> t_out] SKM[(((M #~>) t_in) t_out)]
  -- Polymorphic
  | ccall : HasType lhs t_lhs
    → HasType rhs t_rhs
    → IsValueNoArgStep t_lhs
    → HasType SKM[(lhs rhs)] SKM[(t_lhs rhs)]
  | call  : HasType lhs SKM[t_in ~> t_out]
    → HasType rhs t_in
    → IsValueN n SKM[((t_in ~> t_out) rhs)] t'
    → HasType SKM[(lhs rhs)] t'

namespace IsValue

lemma no_step (h : IsValue e) : ¬ ∃ e', IsEvalOnce e e' := by
  intro ⟨e', h_step⟩
  cases h
  repeat cases h_step
  repeat contradiction
  cases h_step
  repeat contradiction
  have h := AllM.no_step (by assumption)
  simp_all
  case m_arr₁.left h₁ =>
    cases h₁
    repeat contradiction
    simp_all
  cases h_step
  repeat contradiction
  case m_arr.left h =>
    cases h
    repeat contradiction
    case left h =>
      cases h
      repeat contradiction
      have h := AllM.no_step (by assumption)
      simp_all
  cases h_step
  repeat contradiction
  case m_k₁.left h =>
    cases h
    repeat contradiction
    have h := AllM.no_step (by assumption)
    simp_all
  cases h_step
  repeat contradiction
  case m_s₁.left h =>
    cases h
    repeat contradiction
    have h := AllM.no_step (by assumption)
    simp_all
  cases h_step
  repeat contradiction
  case m_s₂.left h =>
    cases h
    repeat contradiction
    case left h =>
      cases h
      repeat contradiction
      have h := AllM.no_step (by assumption)
      simp_all
  cases h_step
  repeat contradiction
  have h := AllM.no_step (by assumption)
  simp_all

end IsValue

namespace IsValueN

lemma final_is_val (h : IsValueN n e e_final) : IsValue e_final := by
  induction n generalizing e
  cases h
  assumption
  case succ n ih =>
    cases h
    case succ e' h_step h_val =>
      exact ih h_val

lemma trans (h₁ : IsValueN n₁ e₁ e₂) (h₂ : IsValueN n₂ e₂ e₃) : IsValueN n₁ e₁ e₂ := by
  induction h₁
  cases h₂
  exact IsValueN.val (by assumption)
  have h := IsValue.no_step (by assumption)
  simp_all
  case succ ih =>
    apply IsValueN.succ
    assumption
    exact ih h₂

end IsValueN

namespace IsValueNoArgStep

lemma all_arg_val (h : IsValueNoArgStep t) : IsValue SKM[(t arg)] := by
  cases h
  exact IsValue.k₁
  exact IsValue.s₁
  exact IsValue.arr₁
  exact IsValue.s₂
  exact IsValue.arr
  exact IsValue.m_k₁ $ by assumption
  exact IsValue.m_s₂ $ by assumption
  exact IsValue.m_s₁ $ by assumption

end IsValueNoArgStep

namespace HasType

lemma all_canonical_norm (h_t : HasType e t) : IsValue t := by
  induction h_t
  exact IsValue.m_comb (by assumption) AllM.m
  exact IsValue.arr
  exact IsValue.arr
  case call lhs t_in t_out rhs n t' h_t_lhs h_t_rhs h_val₁ h_val₂ h_val₃ =>
    exact h_val₁.final_is_val
  case ccall lhs t_rhs rhs t_rhs h_t_lhs h_t_rhs h_no_step ih₁ ih₂ =>
    exact @h_no_step.all_arg_val _ rhs
  apply IsValue.m_comb
  assumption
  exact AllM.m_m
  exact IsValue.m_arr AllM.m

lemma preservation_k (h_t : HasType SKM[((((K α) β) x) y)] t) : HasType x t := by
  cases h_t
  contradiction
  case call h _ _  =>
    cases h
    case call h _ _  =>
      cases h
      case k h =>
        cases h
        case succ h _ =>
          cases h
          case arr h =>
            cases h
            case succ h _ =>
              cases h
              case k h =>
                cases h
                case val h =>
                  cases h
                  contradiction
                  case succ h _ =>
                    cases h
                    case arr h =>
                      cases h
                      case val h =>
                        cases h
                        repeat contradiction
                      case succ h _ =>
                        cases h
                        case k h =>
                          cases h
                          assumption
                          case succ h _ _ _ _ h_step _ =>
                            have h := h.all_canonical_norm.no_step
                            simp_all
                        contradiction
                    contradiction
                contradiction
              contradiction
          contradiction
      contradiction
      contradiction
    contradiction
  case ccall t_lhs t_rhs h_no_step h_t_lhs h_t_rhs =>
    cases h_t_lhs
    contradiction
    case ccall h _ =>
      cases h
      repeat contradiction
      case ccall h _ _ =>
        cases h
        repeat contradiction
      contradiction
    case call h _ _  =>
      cases h
      case k h =>
        cases h
        contradiction
        case succ h _ =>
          cases h
          case arr h =>
            cases h
            contradiction
            case succ h _ =>
              cases h
              case k h =>
                cases h
                contradiction
                case succ h _ _  =>
                  cases h
                  contradiction
                  contradiction
              contradiction
          contradiction
      repeat contradiction

lemma preservation_s (h_t : HasType SKM[((((((S α) β) γ) x) y) z)] t) : HasType SKM[((x z) (y z))] t := by
  cases h_t
  contradiction
  case call h _ _  =>
    cases h
    case call h _ _  =>
      cases h
      case call h _ _ =>
        cases h
        case s h =>
          cases h
          case succ h _ =>
            cases h
            case arr h =>
              cases h
              case succ h _ =>
                cases h
                case k h =>
                  cases h
                  case val h =>
                    cases h
                    case succ h _ =>
                      cases h
                      case arr h =>
                        cases h
                        case succ h _ =>
                          cases h
                          case s h =>
                            cases h
                            case succ h _ =>
                              cases h
                              case left h _ =>
                                cases h
                                case k h =>
                                  cases h
                                  case val h =>
                                    cases h
                                    contradiction
                                    case succ h _ =>
                                      cases h
                                      case arr h =>
                                        cases h
                                        case val h =>
                                          cases h
                                          repeat contradiction
                                        case succ h _ =>
                                          cases h
                                          case s h =>
                                            cases h
                                            

theorem preservation (h_t : HasType e t) (h_eval : IsEvalOnce e e') : HasType e' t := by
  sorry

end HasType
