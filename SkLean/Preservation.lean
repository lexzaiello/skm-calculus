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
import Init.Data.List.Lemmas

/-
## Preservation of typing judgements

For unevaluable expressions, the judgement is trivially held.

Preservation of typing under evaluation of `K` is proven given:
- Evaluation of `K α β (x : α) y = x`
- Evaluation of `(K α β x y).eval_once : α` (by `x : α` and `.eval_once = x`), then
- Preservation of `K α β x y : α` is held
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

/-
Assuming `x : α` is the easy case, but does not prove preservation alone.
-/

lemma k_x_judgement_holds_eval_once (ctx : Ctx) : ∀ α β x y, valid_judgement ctx x α → valid_judgement ctx (Call.mk SK[(((K α) β) x)] y).eval_once α := by
  intro α β x y h_t_x
  unfold Call.eval_once
  repeat unfold NamedSkExpr.to_sk_expr
  simp
  exact h_t_x

/-

Proving preservation in the general case of evaluation requires proving `K α β x y : α → (K α β x y).eval_once : α`.

## Substitution

This lemma becomes tricky once substitution is required. I prove that all substitutions of `(var n) rhs` where `n ≠ 1` are noops. I also prove that all substitutions of `(var 1) rhs = rhs`.
-/

lemma substitute_free_noop : ∀ rhs v n, (Var.mk n) ≠ v → Fall.substitute.substitute_e (.var v) n rhs = (.var v) := by
  intro rhs n h_n_gt_1
  unfold Fall.substitute.substitute_e
  simp
  intro h
  match h : SkExpr.var n with
    | .var (Var.mk n') =>
      simp_all
    | .k _ => contradiction
    | .s _ => contradiction
    | .prp _ => contradiction
    | .ty _ => contradiction
    | .fall _ => contradiction
    | .call _ => contradiction

lemma substitute_bound_1 : ∀ rhs, Fall.substitute.substitute_e (.var (.mk ⟨1⟩)) ⟨1⟩ rhs = rhs := by
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
I generalize this lemmha to all bound variables.
-/

lemma n_eq_imp_bound_rhs : ∀ v n rhs, (.mk n) = v → Fall.substitute.substitute_e (.var v) n rhs = rhs  := by
  intro v n rhs h_v_n_eq
  unfold Fall.substitute.substitute_e
  match v with
    | .mk n' =>
      simp_all

/-

## Combinator evaluation type preservation

Now, I prove that `valid_judgement SK[K α β x y] α → valid_judgement SK[K α β x y].eval_once α` by proving the call is well-typed with type `α`.

Judgements of function application are determined to be true or false by substitution of the `∀` type of the left-hand side of the function call. This would seem to complicate the lemma once an argument to `K` like `ty_k` is provided. `ty_k` is dependent, and contains variables. However, all arguments to `K` are well-typed. Furthermore, free variables cannot be well-typed at a root expression. This implies all well-typed variable arguments are bound, typed variables in the context.

We can use this fact in our larger lemma.

However, the judgement rule allowing `beta_eq t t' → valid_judgement e t → valid_judgement e t` further complicates matters. We defer to the later `SN` proof with `sorry` for most lemmas.

A variable is bound if `ctx[(var n).n - 1] = some t`.
-/

def is_bound (ctx : Ctx) (v : Var) :=
  match v with
    | .mk n => n.toNat > 0 ∧ n.toNat ≤ ctx.length

lemma all_well_typed_var_bound_iff (ctx : Ctx) : ∀ (n : BindId), (∃ t, valid_judgement ctx (.var (.mk n)) t) ↔ is_bound ctx (.mk n) := by
  intro v
  constructor
  intro ⟨t_var, h_t_valid⟩
  unfold is_bound
  split
  simp_all
  cases h_t_valid
  case beta_eq => sorry
  case var n h_n_eq h h_valid =>
    simp [GT.gt] at h
    unfold LT.lt at h
    simp [BindId.instLT] at h
    constructor
    exact h
    calc
      n.toNat = (n.toNat - 1) + 1 := (by simp [@Nat.sub_one_add_one n.toNat (by linarith)])
      _ ≤ ctx.length        := (by linarith)
  intro h_is_bound
  simp [is_bound] at h_is_bound
  use ctx[v.toNat - 1]
  obtain ⟨h_n_pos, h₂⟩ := h_is_bound
  exact valid_judgement.var ctx v (by simp [GT.gt]; unfold LT.lt; simp [BindId.instLT]; exact h_n_pos) (by omega)

lemma shift_indices_bound_noop : ∀ v_n shift_by (depth : ℕ), v_n.toNat ≤ depth → (SkExpr.var (.mk v_n)).with_indices_plus shift_by depth = (SkExpr.var (.mk v_n)) := by
  intro v_n shift_by depth h_is_bound
  simp [SkExpr.with_indices_plus]
  simp_all

lemma all_e_well_typed_bound (ctx : Ctx) : ∀ (e : SkExpr) t shift_by, valid_judgement ctx e t → e.with_indices_plus shift_by ctx.length = e := by
  intro e t shift_by h_judgement_t
  match h : e with
    | .k _ =>
      simp [SkExpr.with_indices_plus]
    | .s _ =>
    simp [SkExpr.with_indices_plus]
    | .prp _ =>
      simp [SkExpr.with_indices_plus]
    | .ty _ =>
      simp [SkExpr.with_indices_plus]
    | .fall (.mk bind_ty body) =>
      unfold SkExpr.with_indices_plus
      simp
      cases h_judgement_t
      case fall t_bind_ty t_body h_t_bind_ty h_t_body =>
        simp [Fall.bind_ty] at h_t_bind_ty
        simp [Fall.body] at h_t_body
        have h := all_e_well_typed_bound (bind_ty :: ctx) bind_ty t_bind_ty shift_by h_t_bind_ty
        simp_all
        have h := all_e_well_typed_bound (bind_ty :: ctx) body t_body shift_by h_t_body
        simp_all
      case beta_eq => sorry
    | .call (.mk lhs rhs) =>
      unfold SkExpr.with_indices_plus
      simp
      cases h_judgement_t
      case call t_lhs h_t_lhs h_t_rhs =>
        simp [all_e_well_typed_bound ctx lhs (.fall t_lhs) shift_by h_t_lhs]
        simp [all_e_well_typed_bound ctx rhs t_lhs.bind_ty shift_by h_t_rhs]
      case beta_eq => sorry
    | .var (.mk n) =>
      have h₀ := h_judgement_t
      cases h_judgement_t
      case beta_eq => sorry
      case var h_idx_valid =>
        have h_bound := (all_well_typed_var_bound_iff ctx n).mp (by
          use ctx[n.toNat - 1]
        )
        unfold is_bound at h_bound
        simp at h_bound
        exact shift_indices_bound_noop n shift_by ctx.length (by simp_all)

/-
Using the fact that all variables that are well-typed are bound, we can say that with_indices_plus preserves the values of the variable. This concludes our lemma of preservation of `K α β x y : α`.
-/

lemma k_judgement_x_imp_judgement_call {m n : ℕ} (ctx : Ctx) : ∀ α β x y, valid_judgement ctx α SK[Type m] → valid_judgement ctx β SK[Type n] → valid_judgement ctx x α → valid_judgement ctx SK[((((K α) β) x) y)] α := by
  intro α β x y t_α t_β t_x
  simp [NamedSkExpr.to_sk_expr] at t_α
  simp [NamedSkExpr.to_sk_expr] at t_β
  have h : valid_judgement ctx SK[((((K α) β) x) y)] ((Fall.mk β α).substitute y).body := (by
    apply valid_judgement.call ctx (Call.mk SK[(((K α) β) x)] y) (.mk β α)
    
    sorry
  )
  simp [NamedSkExpr.to_sk_expr] at *
  simp [Fall.substitute] at h
  simp [Fall.body] at h
  
  sorry

/-
I do the same for \\(S\\).
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
