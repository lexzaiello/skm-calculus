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

I set up some convenience lemmas to prove prservation. Type equivalence of a well-typed `K α β x y` call with the type `α` and its evaluation are established using these lemmas: if `(K α β x y) : α` and `(K α β x y).eval_once : α`, then the typing `α` is preserved.
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

lemma substitute_free_noop : ∀ rhs v n, (Var.mk n) ≠ v → Fall.substitute.substitute_e (.var v) n rhs = (.var v) := by
  intro rhs n h_n_gt_1
  unfold Fall.substitute.substitute_e
  simp
  intro h
  simp_all
  match h : SkExpr.var n with
    | .var (Var.mk n') =>
      simp_all
    | .k _ => contradiction
    | .s _ => contradiction
    | .prp _ => contradiction
    | .ty _ => contradiction
    | .fall _ => contradiction
    | .call _ => contradiction

lemma substitute_bound_1 : ∀ rhs, Fall.substitute.substitute_e (.var (.mk ⟨1⟩)) ⟨1⟩ rhs = rhs.with_indices_plus (.mk 1) := by
  intro rhs
  unfold Fall.substitute.substitute_e
  simp

lemma substitute_prp_noop : ∀ e rhs n, e = SkExpr.prp (.mk) → Fall.substitute.substitute_e e n rhs = e := by
  intro e rhs n h_e_not_var
  unfold Fall.substitute.substitute_e
  rw [h_e_not_var]

lemma substitute_ty_noop : ∀ u e rhs n, e = SkExpr.ty (.mk u) → Fall.substitute.substitute_e e n rhs = e := by
  intro u e rhs n h_e_not_var
  unfold Fall.substitute.substitute_e
  rw [h_e_not_var]

lemma substitute_k_noop : ∀ e rhs n, e = SkExpr.k (.mk) → Fall.substitute.substitute_e e n rhs = e := by
  intro e rhs n h_e_not_var
  unfold Fall.substitute.substitute_e
  rw [h_e_not_var]

lemma substitute_s_noop : ∀ e rhs n, e = SkExpr.s (.mk) → Fall.substitute.substitute_e e n rhs = e := by
  intro e rhs n h_e_not_var
  unfold Fall.substitute.substitute_e
  rw [h_e_not_var]

/-
I generalize this lemma to all bound variables.
-/

lemma n_eq_imp_bound_rhs : ∀ v n rhs, (.mk n) = v → Fall.substitute.substitute_e (.var v) n rhs = rhs.with_indices_plus n  := by
  intro v n rhs h_v_n_eq
  unfold Fall.substitute.substitute_e
  match v with
    | .mk n' =>
      simp_all

/-

## Combinator evaluation type preservation

Now, I prove that `valid_judgement SK[K α β x y] α → valid_judgement SK[K α β x y].eval_once α`.
-/

lemma k_eval_def_eq : ∀ α β x y, (Call.mk SK[(((K α) β) x)] y).eval_once = x := by
  intro α β x y
  unfold Call.eval_once
  repeat unfold NamedSkExpr.to_sk_expr
  simp

lemma k_x_judgement_holds_eval_once (ctx : Ctx) : ∀ α β x y, valid_judgement ctx x α → valid_judgement ctx (Call.mk SK[(((K α) β) x)] y).eval_once α := by
  intro α β x y t
  rw [k_eval_def_eq α β x y]
  exact t

lemma k_judgement_x_imp_judgement_call {m n : ℕ} (ctx : Ctx) : ∀ α β x y, valid_judgement ctx α SK[Type m] → valid_judgement ctx β SK[Type n] → valid_judgement (β :: α :: ctx) x α → valid_judgement ctx SK[((((K α) β) x) y)] α := by
  intro α β x y t_α t_β t_x
  unfold NamedSkExpr.to_sk_expr at t_α
  unfold NamedSkExpr.to_sk_expr at t_β
  apply valid_judgement.call ctx (Call.mk SK[(((K α) β) x)] y) α (.mk β α)
  unfold Call.lhs
  simp
  apply valid_judgement.call ctx (Call.mk SK[((K α) β)] x) SK[∀ y : β, α] (.mk α SK[∀ y : β, α])
  unfold Call.lhs
  simp
  apply valid_judgement.call ctx (Call.mk SK[(K α)] β) SK[∀ x : α, ∀ y : β, α] (.mk SK[Type n] SK[∀ x : α, ∀ y : β, α])
  unfold Call.lhs
  simp
  apply valid_judgement.call ctx (Call.mk SK[K] α) SK[∀ β : (Type n), ∀ x : α, ∀ y : β, α] ty_k_fall
  unfold Call.lhs
  simp
  rw [← ty_k_def_eq]
  exact valid_judgement.k ctx .mk (ty_k) m n rfl
  unfold Fall.bind_ty
  unfold ty_k_fall
  simp
  unfold Call.rhs
  simp
  exact t_α
  repeat unfold NamedSkExpr.to_sk_expr
  unfold Fall.substitute
  unfold ty_k_fall
  simp
  simp [substitute_ty_noop]
  unfold Fall.substitute.substitute_e
  simp [substitute_ty_noop]
  unfold Fall.substitute.substitute_e
  unfold BindId.succ
  simp
  simp [n_eq_imp_bound_rhs]
  unfold Fall.substitute.substitute_e
  unfold BindId.succ
  simp
  simp [n_eq_imp_bound_rhs]
  simp [substitute_free_noop]
  unfold Call.rhs
  simp
  unfold SkExpr.with_indices_plus
  simp
  unfold Fall.body
  simp
  
  sorry

/-
I do the same for S
-/

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
