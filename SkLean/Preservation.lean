/-
# Preservation of SN and Typing Judgements

In order to prove inclusion of all well-typed expressions in our reducibility candidate set, we must first prove:

- That typing judgements are preserved after one-step evaluation
- That membership in the candidate set is preserved after evaluation
-/

import SkLean.Ast
import SkLean.Dsl
import SkLean.Typing
import Mathlib.Tactic

/-
## Preservation of typing judgements

For unevaluable expressions, the judgement is trivially held. The judgement is also trivially held for application of the \\(K\\) combinator.

I set up some convenience lemmas to prove prservation. Type equivalence of a well-typed `K α β x y` call with the type α and its evaluation are established using these lemmas: if `(K α β x y) : α` and `(K α β x y).eval_once : α`, then the typing α is preserved.
-/

lemma k_def_eq : ∀ α β x y, (Call.mk SK[(((K α) β) x)] y).eval_once = x := by
  intro α β x y
  unfold Call.eval_once
  repeat unfold NamedSkExpr.to_sk_expr
  simp

lemma s_def_eq : ∀ α β γ x y z, (Call.mk SK[(((((S α) β) γ) x) y)] z).eval_once = SK[((x z)(y z))] := by
  intro α β x y γ
  unfold Call.eval_once
  repeat unfold NamedSkExpr.to_sk_expr
  simp

lemma type_k_eval_def_eq (ctx : Ctx) : ∀ α β x y, valid_judgement ctx x α → valid_judgement ctx (Call.mk SK[(((K α) β) x)] y).eval_once α := by
  intro α β x y h_t_x
  unfold Call.eval_once
  repeat unfold NamedSkExpr.to_sk_expr
  simp
  exact h_t_x

/-

## Substitution

This lemma becomes tricky once substitution is required. I prove that all substitutions of `(var n) rhs` where `n ≠ 1` are noops. I also prove that all substitutions of `(var 1) rhs) = rhs`.
-/

lemma substitute_free_noop : ∀ rhs n, n > 1 → Fall.substitute.substitute_e (.var (.mk ⟨n⟩)) ⟨1⟩ rhs = (.var (.mk ⟨n⟩)) := by
  intro rhs n h_n_gt_1
  unfold Fall.substitute.substitute_e
  simp
  intro h
  simp_all

lemma substitute_bound_1 : ∀ rhs, Fall.substitute.substitute_e (.var (.mk ⟨1⟩)) ⟨1⟩ rhs = rhs.with_indices_plus (.mk 1) := by
  intro rhs
  unfold Fall.substitute.substitute_e
  simp

/-

## K evaluation type preservation

Now, I prove that `valid_judgement SK[K α β x y] α → valid_judgement SK[K α β x y].eval_once α`.
-/

lemma type_k_def_eq {m n : ℕ} (ctx : Ctx) : ∀ α β x y, valid_judgement ctx α (.ty (.mk m)) → valid_judgement ctx β (.ty (.mk n)) → valid_judgement ctx x α → valid_judgement ctx y β → valid_judgement ctx SK[((((K α) β) x) y)] α := by
  intro α β x y h_t_α h_t_β h_t_x h_t_y
  repeat unfold NamedSkExpr.to_sk_expr
  apply valid_judgement.call ctx (Call.mk SK[(((K α) β) x)] y) α (Fall.mk β α)
  unfold Call.lhs
  simp
  apply valid_judgement.call ctx (Call.mk SK[((K α) β)] x) (SkExpr.fall (Fall.mk β α)) (Fall.mk α SK[∀ y : β, α])
  repeat unfold NamedSkExpr.to_sk_expr
  unfold Call.lhs
  simp
  apply valid_judgement.call ctx (Call.mk SK[(K α)] β) SK[∀ x : α, ∀ y : β, α] (Fall.mk (.ty (.mk n)) SK[∀ x : α, ∀ y : β, α])
  unfold Call.lhs
  simp
  apply valid_judgement.call ctx (Call.mk (.k .mk) α) SK[∀ β : (Type n), ∀ x : α, ∀ y : β, α] (@ty_k_fall m n)
  unfold Call.lhs
  simp
  rw [← ty_k_def_eq]
  exact valid_judgement.k ctx (.mk) ty_k m n (rfl)
  unfold Call.rhs
  simp
  unfold ty_k_fall
  unfold Fall.bind_ty
  simp
  exact h_t_α
  unfold ty_k_fall
  unfold Fall.body
  
  sorry

lemma type_s_def_eq (ctx : Ctx

lemma k_judgement_holds_eval_once (ctx : Ctx) : ∀ α β x y t, valid_judgement ctx SK[((((K α) β) x) y)] t → valid_judgement ctx (Call.mk SK[(((K α) β) x)] y).eval_once t := by
  intro α β x y t h_t_holds
  repeat unfold NamedSkExpr.to_sk_expr at *
  unfold Call.eval_once
  simp
  cases h_t_holds
  case call t_lhs h_t_lhs h_t_rhs h_t =>
    unfold Call.lhs at *
    simp_all
    unfold Fall.substitute at *
    cases t_lhs
    case mk =>
    simp_all
    
    sorry
  sorry

lemma judgement_holds_eval_once (ctx : Ctx) : ∀ (call : Call) (t : SkExpr), valid_judgement ctx (.call call) t ↔ valid_judgement ctx call.eval_once t := by
  intro c t
  unfold Call.eval_once
  split
  case h_1 α β x y =>
    constructor
    intro h
    cases h
    case mp.call =>
    
    sorry

lemma eval_once_candidate_iff (ctx : Ctx) : ∀ (call : Call) (t : SkExpr), is_candidate_for_t ctx (.call call) t ↔ is_candidate_for_t ctx (call.eval_once) t := by
  intro e t
  constructor
  case mp =>
    intro h
    match h with
      | .fn e' t' t_judgement arg h_t_arg h_redux => sorry
      | .ty e' t' ht' =>
        have h_judgement_t := candidate_for_t_imp_judgement_t ctx (.call e) t h
        -- Since 
        sorry
      | .prp _ _ _ => sorry
      | .fall _ _ _ => sorry
  case mpr =>
    intro h
    sorry
