import SkLean.Ast3
import SkLean.Eval

inductive IsComb : Ast.Expr → Prop
  | k   : IsComb SKM[K]
  | s   : IsComb SKM[S]
  | m   : IsComb SKM[M]
  | arr : IsComb SKM[#~>]

inductive IsSingle : Ast.Expr → Prop
  | comb : IsComb e → IsSingle e
  | prp  : IsSingle SKM[Prp]
  | ty   : IsSingle SKM[Ty n]

namespace IsComb

@[simp]
lemma no_step (h : IsComb e) : ¬ ∃ e', Expr.eval_once e = .some e' := by
  cases h
  repeat (intro ⟨e', h⟩; cases h)

end IsComb

inductive IsValue : Ast.Expr → Prop
  | single : IsSingle e → IsValue e
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
  | m_k₁   : IsValue SKM[((M K) α)]
  | m_s₁   : IsValue SKM[((M S) α)]
  | m_s₂   : IsValue SKM[(((M S) α) β)]
  | m_comb : IsComb e
    → IsValue SKM[(M e)]

inductive IsValueNoArgStep : Ast.Expr → Prop
  | k    : IsValueNoArgStep SKM[K]
  | s    : IsValueNoArgStep SKM[S]
  | arr  : IsValueNoArgStep SKM[#~>]
  | s₁   : IsValueNoArgStep SKM[(S α)]
  | arr₁ : IsValueNoArgStep SKM[(#~> _α)]
  | m_k₁ : IsValueNoArgStep SKM[(M K)]
  | m_s₁ : IsValueNoArgStep SKM[((M S) α)]

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
    → HasType SKM[((K α) β)] SKM[(α ~> (((K (Ty 0)) α) (β ~> (((K t_α) β) α))))]
  | s     : HasType α t_α
    → HasType β t_β
    → HasType γ t_γ
    → HasType SKM[(((S α) β) γ)] SKM[(α ~> ((((K (Ty 0))) α) (β ~> ((((K (Ty 0)) β) (γ ~> (((((S t_α) t_β) γ) α) β)))))))]
  | m_m   : IsComb e
    → HasType SKM[(M e)] SKM[Prp]
  | prp   : HasType SKM[Prp] SKM[Ty 0]
  | ty    : HasType SKM[Ty n] SKM[Ty n.succ]
  | arr   : HasType SKM[t_in ~> t_out] SKM[Ty 0]
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
  apply IsValue.k₁
  apply IsValue.s₁
  apply IsValue.arr₁
  apply IsValue.s₂
  apply IsValue.arr
  apply IsValue.m_k₁
  apply IsValue.m_s₂

end IsValueNoArgStep

namespace HasType

lemma all_canonical_norm (h_t : HasType e t) : IsValue t := by
  induction h_t
  exact IsValue.m_comb (by assumption)
  exact IsValue.arr
  exact IsValue.arr
  exact IsValue.single (IsSingle.prp)
  repeat exact IsValue.single (IsSingle.ty)
  case call lhs t_in t_out rhs n t' h_t_lhs h_t_rhs h_val₁ h_val₂ h_val₃ =>
    exact h_val₁.final_is_val
  case ccall lhs t_rhs rhs t_rhs h_t_lhs h_t_rhs h_no_step ih₁ ih₂ =>
    exact @h_no_step.all_arg_val _ rhs

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
                        contradiction
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
                          case k h =>
                            cases h
                            case val h =>
                              cases h
                              contradiction
                              case succ h =>
                                cases h
                                case val h _ =>
                                  cases h
                                  contradiction
                                  contradiction
                                case succ h _ _ _ _ =>
                                  cases h
                                  case arr h =>
                                    cases h
                                    case s h =>
                                      cases h
                                      

theorem preservation (h_t : HasType e t) (h_eval : IsEvalOnce e e') : HasType e' t := by
  sorry

end HasType
