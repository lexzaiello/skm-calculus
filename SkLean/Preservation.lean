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

Judgements of function application are determined to be true or false by substitution of the `∀` type of the left-hand side of the function call. This would seem to complicate the lemma once an argument to `K` like `ty_k` is provided. `ty_k` is dependent, and contains variables. However, all arguments to `K` are well-typed. This implies all variables that could show up in arguments are typed in the context. This implies all variables within the scope of an argument are bound. We can use this fact in our larger lemma.

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
    simp [List.getElem?_eq_some_iff] at h_valid
    obtain ⟨h_n_length, h_has_t⟩ := h_valid
    have h_length_pos := @List.length_pos_of_mem SkExpr t_var ctx (by rw [← h_has_t]; simp)
    unfold GT.gt at h
    unfold LT.lt at h
    simp [BindId.instLT] at h
    simp [h]
    calc
      n.toNat = (n.toNat - 1) + 1 := (by simp [@Nat.sub_one_add_one n.toNat (by linarith)])
      _ ≤ ctx.length        := (by linarith)
  intro h_is_bound
  simp [is_bound] at h_is_bound
  use ctx[v.toNat - 1]
  obtain ⟨h_n_pos, h₂⟩ := h_is_bound
  exact valid_judgement.var ctx v ctx[v.toNat - 1] (by simp [GT.gt]; unfold LT.lt; simp [BindId.instLT]; exact h_n_pos) (by simp)

lemma shift_indices_bound_noop (ctx : Ctx) : ∀ v_n shift_by, is_bound ctx (.mk v_n) → (SkExpr.var (.mk v_n)).with_indices_plus shift_by (ctx.length) = (SkExpr.var (.mk v_n)) := by
  intro v_n shift_by h_is_bound
  simp [SkExpr.with_indices_plus]
  intro h_is_bound'
  sorry

lemma all_e_well_typed_bound (ctx : Ctx) : ∀ (e : SkExpr) t shift_by depth, depth = ctx.length → valid_judgement ctx e t → e.with_indices_plus shift_by depth = e := by
  intro e t shift_by depth h_depth_valid h_judgement_t
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
      case fall t_bind_ty t_body h_t_bind_ty h_t_body h_t_rfl =>
        simp [Fall.bind_ty] at h_t_bind_ty
        simp [Fall.body] at h_t_body
        have h_depth : depth + 1 = (bind_ty :: ctx).length := by
          simp [h_depth_valid]
        constructor
        simp [all_e_well_typed_bound (bind_ty :: ctx) bind_ty t_bind_ty shift_by (depth + 1) h_depth h_t_bind_ty]
        simp [all_e_well_typed_bound (bind_ty :: ctx) body t_body shift_by (depth + 1) h_depth h_t_body]
      case beta_eq => sorry
    | .call (.mk lhs rhs) =>
      unfold SkExpr.with_indices_plus
      simp
      cases h_judgement_t
      case call t_lhs h_t_lhs h_t_rhs h_t_eq =>
        simp [all_e_well_typed_bound ctx lhs (.fall t_lhs) shift_by (depth) h_depth_valid h_t_lhs]
        simp [all_e_well_typed_bound ctx rhs t_lhs.bind_ty shift_by (depth) h_depth_valid h_t_rhs]
      case beta_eq => sorry
    | .var (.mk n) =>
      have h₀ := h_judgement_t
      cases h_judgement_t
      case beta_eq => sorry
      case var h_idx_valid =>
        have h_bound := (all_well_typed_var_bound_iff ctx n).mp (by
          use t
        )
        unfold is_bound at h_bound
        simp at h_bound
        rw [h_depth_valid]
        exact shift_indices_bound_noop n shift_by (ctx.length) (by sorry)

/-
Using the fact that all variables that are well-typed are bound, we can say that with_indices_plus preserves the values of the variable. This concludes our lemma of preservation of `K α β x y : α`.
-/

lemma k_judgement_x_imp_judgement_call {m n : ℕ} (ctx : Ctx) : ∀ α β x y, valid_judgement ctx α SK[Type m] → valid_judgement ctx β SK[Type n] → valid_judgement ctx x α → valid_judgement ctx SK[((((K α) β) x) y)] α := by
  intro α β x y t_α t_β t_x
  simp [NamedSkExpr.to_sk_expr] at t_α
  simp [NamedSkExpr.to_sk_expr] at t_β
  apply valid_judgement.call ctx (Call.mk SK[(((K α) β) x)] y) α (.mk β α)
  simp [Call.lhs]
  apply valid_judgement.call ctx (Call.mk SK[((K α) β)] x) SK[∀ y : β, α] (.mk α SK[∀ y : β, α])
  simp [Call.lhs]
  apply valid_judgement.call ctx (Call.mk SK[(K α)] β) SK[∀ x : α, ∀ y : β, α] (.mk SK[Type n] (.fall (Fall.mk α (.fall (.mk (.var (.mk ⟨3⟩)) α)))))
  simp [Call.lhs]
  apply valid_judgement.call ctx (Call.mk SK[K] α) SK[∀ β : (Type n), ∀ x : α, ∀ y : #β, α] ty_k_fall
  simp [Call.lhs]
  rw [← ty_k_def_eq]
  exact valid_judgement.k ctx .mk (ty_k) m n rfl
  simp [Fall.bind_ty]
  simp [ty_k_fall]
  simp [Call.rhs]
  exact t_α
  simp [NamedSkExpr.to_sk_expr]
  simp [Call.rhs]
  simp [ty_k_fall]
  simp [Fall.body]
  simp [Fall.substitute]
  simp [Fall.substitute.substitute_e]
  simp [BindId.succ]
  simp [shift_indices_bound_noop]
  sorry
  simp [Call.rhs]
  simp [NamedSkExpr.to_sk_expr]
  simp [Fall.bind_ty]
  exact t_β
  simp [NamedSkExpr.to_sk_expr]
  simp [Call.rhs]
  simp [Fall.substitute]
  simp [Fall.substitute.substitute_e]
  simp [BindId.succ]
  simp [Fall.body]
  
  sorry
  sorry
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
