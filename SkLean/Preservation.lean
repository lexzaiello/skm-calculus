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

lemma k_x_judgement_holds_eval_once : ∀ α β x y, valid_judgement [] x α → valid_judgement [] (Call.mk SK[(((K α) β) x)] y).eval_once α := by
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
I generalize this lemma to all bound variables.
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

Judgements of function application are determined to be true or false by substitution of the `∀` type of the left-hand side of the function call. This would seem to complicate the lemma once an argument to `K` like `ty_k` is provided. `ty_k` is dependent, and contains variables. However, all arguments to `K` are well-typed and closed. I demonstrate this later.

We can use this fact in our larger lemma.

However, the judgement rule allowing `beta_eq t t' → valid_judgement e t → valid_judgement e t` further complicates matters. We defer to the later `SN` proof with `sorry` for most lemmas.

A variable is bound if `ctx[(var n).n - 1] = some t`.
-/

inductive is_bound : Ctx → SkExpr → Prop
  | var  ctx n   : n.toNat > 0 → ⟨(n.toNat - 1)⟩ < (BindId.mk ctx.length) → is_bound ctx (.var (.mk n))
  | app  ctx c   : is_bound ctx c.lhs → is_bound ctx c.rhs → is_bound ctx (.call c)
  | fall ctx f   : is_bound (f.bind_ty :: ctx) f.bind_ty → is_bound (f.bind_ty :: ctx) f.body → is_bound ctx (.fall f)
  | k    ctx k   : is_bound ctx (.k k)
  | s    ctx s   : is_bound ctx (.s s)
  | prp  ctx prp : is_bound ctx (.prp prp)
  | ty   ctx ty  : is_bound ctx (.ty ty)

lemma all_well_typed_var_bound_iff (ctx : Ctx) : ∀ (n : BindId), (∃ t, valid_judgement ctx (.var (.mk n)) t) ↔ is_bound ctx (.var (.mk n)) := by
  intro v
  constructor
  intro ⟨t_var, h_t_valid⟩
  cases h_t_valid
  case mp.beta_eq => sorry
  case mp.var h_pos h_in_bounds =>
    apply is_bound.var ctx
    if h : v = { toNat := ctx.length } then
      simp_all
    else
      simp_all
      rw [LT.lt] at h_pos
      simp [BindId.instLT] at h_pos
      simp_all
    rw [LT.lt]
    simp [BindId.instLT]
    exact h_in_bounds
  case mpr =>
    intro h_bound
    cases h_bound
    use ctx[v.toNat - 1]
    apply valid_judgement.var
    simp [GT.gt]
    rw [LT.lt]
    simp [BindId.instLT]
    simp_all

/-
I generalize this lemma to all expressions by induction on the definition of being bound.
-/

lemma all_well_typed_e_bound_iff (ctx : Ctx) : ∀ e, (∃ t, valid_judgement ctx e t) → is_bound ctx e := by
  intro e h_typed
  cases e
  case k =>
    simp [is_bound.k]
  case s =>
    simp [is_bound.s]
  case prp =>
    simp [is_bound.prp]
  case ty =>
    simp [is_bound.ty]
  case fall f =>
    obtain ⟨t, h_valid_t⟩ := h_typed
    match f with
      | .mk bind_ty body =>
        cases h_valid_t
        case fall t_bind_ty h_bind_ty h_body =>
          simp [Fall.bind_ty] at h_bind_ty
          simp [Fall.body] at h_body
          apply is_bound.fall
          apply all_well_typed_e_bound_iff
          use t_bind_ty
          simp [Fall.bind_ty]
          exact h_bind_ty
          apply all_well_typed_e_bound_iff
          use t
          simp [Fall.body]
          exact h_body
        case beta_eq => sorry
  case call c =>
    obtain ⟨t, h_valid_t⟩ := h_typed
    match c with
      | .mk lhs rhs =>
        cases h_valid_t
        case call t_lhs h_t_lhs h_t_rhs  =>
          simp [Call.lhs] at h_t_lhs
          simp [Call.rhs] at h_t_rhs
          apply is_bound.app
          apply all_well_typed_e_bound_iff
          use (.fall t_lhs)
          exact h_t_lhs
          apply all_well_typed_e_bound_iff
          use t_lhs.bind_ty
          exact h_t_rhs
        case beta_eq => sorry
  case var v =>
    obtain ⟨t, h_valid_t⟩ := h_typed
    match v with
      | .mk n =>
        cases h_valid_t
        case var h_pos h_bound  =>
          apply is_bound.var
          simp [GT.gt] at h_pos
          rw [LT.lt] at h_pos
          simp [BindId.instLT] at h_pos
          exact h_pos
          rw [LT.lt]
          simp [BindId.instLT]
          exact h_bound
        case beta_eq => sorry

lemma shift_indices_bound_noop : ∀ v_n shift_by (depth : ℕ), v_n.toNat ≤ depth → (SkExpr.var (.mk v_n)).with_indices_plus shift_by depth = (SkExpr.var (.mk v_n)) := by
  intro v_n shift_by depth h_is_bound
  simp [SkExpr.with_indices_plus]
  simp_all

lemma all_e_well_typed_bound_shift_noop (ctx : Ctx) : ∀ (e : SkExpr) t shift_by, valid_judgement ctx e t → e.with_indices_plus shift_by ctx.length = e := by
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
      case fall t_bind_ty h_t_bind_ty h_t =>
        simp [Fall.bind_ty] at h_t_bind_ty
        simp [Fall.body] at h_t
        have h := all_e_well_typed_bound_shift_noop (bind_ty :: ctx) bind_ty t_bind_ty shift_by h_t_bind_ty
        simp_all
        have h := all_e_well_typed_bound_shift_noop (bind_ty :: ctx) body t shift_by (by simp [Fall.bind_ty] at h_t; exact h_t)
        simp_all
      case beta_eq => sorry
    | .call (.mk lhs rhs) =>
      unfold SkExpr.with_indices_plus
      simp
      cases h_judgement_t
      case call t_lhs h_t_lhs h_t_rhs =>
        simp [all_e_well_typed_bound_shift_noop ctx lhs (.fall t_lhs) shift_by h_t_lhs]
        simp [all_e_well_typed_bound_shift_noop ctx rhs t_lhs.bind_ty shift_by h_t_rhs]
      case beta_eq => sorry
    | .var (.mk n) =>
      have h₀ := h_judgement_t
      cases h_judgement_t
      case beta_eq => sorry
      case var h_idx_valid =>
        have h_bound := (all_well_typed_var_bound_iff ctx n).mp (by
          use ctx[n.toNat - 1]
        )
        cases h_bound
        case var h_pos h_bound =>
          rw [LT.lt] at h_bound
          simp [BindId.instLT] at h_bound
          exact shift_indices_bound_noop n shift_by ctx.length (by rw [← Nat.pred_eq_sub_one] at h_bound; exact Nat.le_of_pred_lt h_bound)

/-
Using the above lemma, we can prove that substitution of all bound variables is a noop.
-/

lemma substitute_bound_noop (ctx : Ctx) : ∀ e with_expr, is_bound ctx e → Fall.substitute.substitute_e e ⟨ctx.length + 1⟩ with_expr = e := by
  intro e with_expr h_bound
  cases e
  case k  =>
    simp [Fall.substitute.substitute_e]
  case s =>
    simp [Fall.substitute.substitute_e]
  case prp =>
    simp [Fall.substitute.substitute_e]
  case ty =>
    simp [Fall.substitute.substitute_e]
  case fall f =>
    match f with
      | .mk bind_ty body =>
        cases h_bound
        case fall h_bind_ty_bound h_body_bound =>
          simp [Fall.substitute.substitute_e]
          constructor
          exact substitute_bound_noop (bind_ty :: ctx) bind_ty with_expr h_bind_ty_bound
          exact substitute_bound_noop (bind_ty :: ctx) body with_expr h_body_bound
  case call c =>
    match c with
      | .mk lhs rhs =>
        cases h_bound
        case app h_bound_lhs h_bound_rhs =>
          simp [Fall.substitute.substitute_e]
          constructor
          exact (substitute_bound_noop ctx lhs with_expr h_bound_lhs)
          exact (substitute_bound_noop ctx rhs with_expr h_bound_rhs)
  case var v =>
    match h : v with
      | .mk n =>
        cases h_bound
        case var h_bound =>
          unfold Fall.substitute.substitute_e
          simp
          have h_bound' : (BindId.mk n.toNat) ≤ { toNat := ctx.length } := by
            rw [LT.lt] at h_bound
            simp [BindId.instLT] at h_bound
            rw [LE.le]
            simp [BindId.instLE]
            omega
          have h_bound'' : (BindId.mk n.toNat) < { toNat := ctx.length + 1 } := by
            simp_all
            rw [LT.lt]
            simp [BindId.instLT]
            rw [LE.le] at h_bound'
            simp [BindId.instLE] at h_bound'
            linarith
          have h_bound''' : n < { toNat := ctx.length + 1 } := by
            simp_all
          simp_all
          intro h
          rw [h] at h_bound'''
          exfalso
          rw [LT.lt] at h_bound'''
          simp [BindId.instLT] at h_bound'''

/-
Using the fact that all variables that are well-typed are bound, we can say that with_indices_plus preserves the values of the variable. This concludes our lemma of preservation of `K α β x y : α`.

### Inconsistency

It should be noted that the judgement `(K α β x y).eval_once : α` is obviously true, as evaluation of the `K` combinator requires no substitution, and leaves `α` unaltered. However, `(K α β x y) : α` can potentially perform substitution, if `α` contains free variables. However, **`K` and `S` are closed and contain no free variables.**

Closed expressions do not contain free variables, and as a result, are well-typed at their roots with the same type under any context.

TODO: Clean this lemma up a ton.
-/

lemma judgement_holds_closed_any : ∀ ctx ctxxs e t, valid_judgement ctx e t  ↔ valid_judgement (ctx ++ ctxxs) e t := by
  intro ctx ctxxs e t
  constructor
  intro h_closed
  cases e
  case k a =>
    cases h_closed
    case k =>
      simp [valid_judgement.k]
    case beta_eq => sorry
  case s a =>
    cases h_closed
    case s =>
      simp [valid_judgement.s]
    case beta_eq => sorry
  case prp a =>
    cases h_closed
    case prp =>
      simp [valid_judgement.prp]
    case beta_eq => sorry
  case ty a =>
    cases h_closed
    case ty =>
      simp [valid_judgement.ty]
    case beta_eq => sorry
  case fall f =>
    match f with
      | .mk bind_ty body =>
        cases h_closed
        case fall t_bind_ty h_t_bind_ty h_t_body =>
          simp [Fall.body] at *
          simp [Fall.bind_ty] at *
          apply valid_judgement.fall (ctx ++ ctxxs) (.mk bind_ty body) t_bind_ty t
          have h := (judgement_holds_closed_any [(Fall.mk bind_ty body).bind_ty] ctx (Fall.mk bind_ty body).bind_ty t_bind_ty).mpr h_t_bind_ty
          have h := (judgement_holds_closed_any [(Fall.mk bind_ty body).bind_ty] (ctx ++ ctxxs) (Fall.mk bind_ty body).bind_ty t_bind_ty).mp h
          exact h
          have h := (judgement_holds_closed_any [(Fall.mk bind_ty body).bind_ty] ctx (Fall.mk bind_ty body).body t).mpr h_t_body
          have h := (judgement_holds_closed_any [(Fall.mk bind_ty body).bind_ty] (ctx ++ ctxxs) (Fall.mk bind_ty body).body t).mp h
          exact h
        case beta_eq => sorry
  case call c =>
    match c with
      | .mk lhs rhs =>
        cases h_closed
        case call t_lhs h_t_lhs h_t_rhs =>
          apply valid_judgement.call (ctx ++ ctxxs) (.mk lhs rhs) t_lhs
          simp [Call.lhs] at *
          have h := (judgement_holds_closed_any ctx ctxxs lhs (SkExpr.fall t_lhs)).mp h_t_lhs
          exact h
          have h := (judgement_holds_closed_any ctx ctxxs rhs t_lhs.bind_ty).mp h_t_rhs
          exact h
        case beta_eq => sorry
  case var _ => sorry
  intro h_closed
  cases e
  case k a =>
    cases h_closed
    case k =>
      simp [valid_judgement.k]
    case beta_eq => sorry
  case s a =>
    cases h_closed
    case s =>
      simp [valid_judgement.s]
    case beta_eq => sorry
  case prp a =>
    cases h_closed
    case prp =>
      simp [valid_judgement.prp]
    case beta_eq => sorry
  case ty a =>
    cases h_closed
    case ty =>
      simp [valid_judgement.ty]
    case beta_eq => sorry
  case fall f =>
    match f with
      | .mk bind_ty body =>
        cases h_closed
        case fall t_bind_ty h_t_bind_ty h_t_body =>
          apply valid_judgement.fall ctx (.mk bind_ty body) t_bind_ty t
          have h := (judgement_holds_closed_any [(Fall.mk bind_ty body).bind_ty] (ctx ++ ctxxs) (Fall.mk bind_ty body).bind_ty t_bind_ty).mpr h_t_bind_ty
          have h := (judgement_holds_closed_any [(Fall.mk bind_ty body).bind_ty] (ctx) (Fall.mk bind_ty body).bind_ty t_bind_ty).mp h
          exact h
          have h := (judgement_holds_closed_any [(Fall.mk bind_ty body).bind_ty] (ctx ++ ctxxs) (Fall.mk bind_ty body).body t).mpr h_t_body
          have h := (judgement_holds_closed_any [(Fall.mk bind_ty body).bind_ty] ctx (Fall.mk bind_ty body).body t).mp h
          exact h
        case beta_eq => sorry
  case call c =>
    match c with
      | .mk lhs rhs =>
        cases h_closed
        case call t_lhs h_t_lhs h_t_rhs =>
          apply valid_judgement.call ctx (.mk lhs rhs) t_lhs
          simp [Call.lhs] at *
          have h := (judgement_holds_closed_any ctx ctxxs lhs (SkExpr.fall t_lhs)).mpr h_t_lhs
          exact h
          have h := (judgement_holds_closed_any ctx ctxxs rhs t_lhs.bind_ty).mpr h_t_rhs
          exact h
        case beta_eq => sorry
  case var _ => sorry

lemma k_judgement_x_imp_judgement_call {m n : ℕ} : ∀ α β x y, valid_judgement [] α SK[Type m] → valid_judgement [] β SK[Type n] → valid_judgement [] x α → valid_judgement [] y β → valid_judgement [] SK[((((K α) β) x) y)] α := by
  intro α β x y t_α t_β t_x t_y
  simp [NamedSkExpr.to_sk_expr] at t_α
  simp [NamedSkExpr.to_sk_expr] at t_β
  have h : valid_judgement [] SK[((((K α) β) x) y)] ((Fall.mk β α).substitute y).body := (by
    apply valid_judgement.call [] (Call.mk SK[(((K α) β) x)] y) (.mk β α)
    simp [NamedSkExpr.to_sk_expr] at *
    simp [Call.lhs]
    have h : (valid_judgement [] (SkExpr.call (Call.mk (SkExpr.call (Call.mk (SkExpr.call (Call.mk (SkExpr.k «K».mk) α)) β)) x))
    ((Fall.mk α (SkExpr.fall (Fall.mk β α))).substitute
        (Call.mk (SkExpr.call (Call.mk (SkExpr.call (Call.mk (SkExpr.k «K».mk) α)) β)) x).rhs).body) := (by
      apply valid_judgement.call [] (Call.mk (SkExpr.call (Call.mk (SkExpr.call (Call.mk (SkExpr.k «K».mk) α)) β)) x) (.mk α (.fall (.mk β α)))
      simp [Call.lhs]
      have h : (valid_judgement [β, SK[Type n], α, SK[Type m]] SK[((K α) β)] ((Fall.mk SK[Type n] (.fall (.mk α (.fall (.mk (SkExpr.var (.mk ⟨3⟩)) α))))).substitute (Call.mk SK[(K α)] β).rhs).body) := (by
        simp [Fall.substitute]
        simp [Fall.substitute.substitute_e]
        simp [BindId.succ]
        simp [NamedSkExpr.to_sk_expr]
        simp [substitute_ty_noop]
        simp [Call.rhs]
        simp [Fall.body]
        have h := substitute_bound_noop [SK[Type m]] α (β.with_indices_plus { toNat := 1 } 0) (by simp [NamedSkExpr.to_sk_expr]; apply all_well_typed_e_bound_iff; use SK[Type m]; simp [NamedSkExpr.to_sk_expr]; exact (judgement_holds_closed_any List.nil [SK[Type m]] α SK[Type m]).mp t_α)
        simp at h
        simp [h]
        have h := all_e_well_typed_bound_shift_noop [SK[Type n], α, SK[Type m]] β SK[Type n] ⟨1⟩ (by simp [NamedSkExpr.to_sk_expr]; exact (judgement_holds_closed_any List.nil [SkExpr.ty (Ty.mk n), α, SkExpr.ty (Ty.mk m)] β SK[Type n]).mp t_β)
        simp at h
        have h := valid_judgement.call [] (.mk SK[(K α)] β) (.mk SK[Type n] (.fall (.mk α (.fall (.mk (.var (.mk ⟨3⟩)) α))))) (by
          simp [Call.lhs]
          simp [NamedSkExpr.to_sk_expr]
          have h : (valid_judgement [] (.call (.mk (SkExpr.k .mk) α)) (.fall (.mk SK[Type n] (.fall (.mk α (.fall (.mk (.var (.mk ⟨3⟩)) α))))))) := by
            have h : valid_judgement [SK[Type m]] (SkExpr.call (Call.mk (SkExpr.k «K».mk) α)) ((@ty_k_fall m n).substitute (Call.mk (SkExpr.k «K».mk) α).rhs).body := by
              simp [NamedSkExpr.to_sk_expr]
              apply valid_judgement.call [SK[Type m]] (.mk (.k .mk) α) ty_k_fall
              simp [Call.lhs]
              rw [← ty_k_def_eq]
              simp [valid_judgement.k]
              simp [Call.rhs]
              unfold ty_k_fall
              simp [Fall.bind_ty]
              exact (judgement_holds_closed_any List.nil [SK[Type m]] α SK[Type m]).mp t_α
            have h := valid_judgement.call [] (.mk (SkExpr.k «K».mk) α) (@ty_k_fall m n) (by simp [Call.lhs]; rw [← ty_k_def_eq]; simp [valid_judgement.k]) (by simp [Call.rhs, ty_k_fall, Fall.bind_ty, NamedSkExpr.to_sk_expr]; exact t_α)
            simp at h
            unfold ty_k_fall at h
            simp [Fall.body] at h
            simp [Call.rhs] at h
            simp [Fall.substitute] at h
            simp [Fall.substitute.substitute_e] at h
            simp [BindId.succ] at h
            have h_shift := all_e_well_typed_bound_shift_noop [] α SK[Type m] ⟨1⟩ t_α
            simp at h_shift
            simp [h_shift] at h
            simp [NamedSkExpr.to_sk_expr]
            exact h
          exact h
        ) t_β
        simp [NamedSkExpr.to_sk_expr, Fall.substitute, substitute_ty_noop, Fall.substitute.substitute_e, BindId.succ, Call.rhs, Fall.body] at h
        simp [*] at h
        exact (judgement_holds_closed_any List.nil [β, SkExpr.ty (Ty.mk n), α, SkExpr.ty (Ty.mk m)] SK[((K α) β)]
          ((.fall (.mk α (.fall (.mk (β.with_indices_plus { toNat := 1 } 0) (Fall.substitute.substitute_e α { toNat := 3 } (β.with_indices_plus { toNat := 1 } 0)))))))).mp h
      )
      simp [NamedSkExpr.to_sk_expr] at h
      simp [Fall.substitute] at h
      simp [Call.rhs] at h
      simp [substitute_ty_noop] at h
      simp [Fall.substitute.substitute_e, BindId.succ, Fall.body] at h
      have h_α_sub_noop := 
      sorry
      sorry
    )
    simp [Fall.substitute, Fall.substitute.substitute_e, Call.rhs, BindId.succ, Fall.body] at h
    have h_sub_noop_h := substitute_bound_noop [α] β (x.with_indices_plus { toNat := 1 } 0) sorry
    simp at h_sub_noop_h
    rw [h_sub_noop_h] at h
    have h_sub_noop_h := substitute_bound_noop [α] α (x.with_indices_plus { toNat := 1 } 0) sorry
    simp at h_sub_noop_h
    rw [h_sub_noop_h] at h
    exact h
    simp [Fall.bind_ty]
    simp [NamedSkExpr.to_sk_expr, Call.rhs]
    exact t_y
  )
  simp [NamedSkExpr.to_sk_expr] at *
  simp [Fall.substitute] at h
  simp [Fall.body] at h
  have h_sub_alpha_noop := substitute_bound_noop [] α (y.with_indices_plus { toNat := 1 } 0) (by
    cases α
    case k =>
      simp [is_bound.k]
    case s =>
      simp [is_bound.s]
    case prp =>
      simp [is_bound.prp]
    case ty =>
      simp [is_bound.ty]
    case fall f =>
      match f with
        | .mk bind_ty body =>
          cases t_α
          case fall t_bind_ty h_t_bind_ty h_t_body =>
            apply is_bound.fall
            simp [Fall.bind_ty]
            apply all_well_typed_e_bound_iff
            use t_bind_ty
            simp [Fall.bind_ty] at h_t_bind_ty
            exact h_t_bind_ty
            apply all_well_typed_e_bound_iff
            use (SkExpr.ty (Ty.mk m))
          case beta_eq =>
            sorry
    case call c =>
      match h_c : c with
        | .mk lhs rhs =>
          -- call lhs rhs is surely of type Ty n
          -- this implies lhs's type is of the form ∀
          apply all_well_typed_e_bound_iff
          use (.ty (Ty.mk m))
    case var v =>
      match v with
        | .mk n =>
          apply (all_well_typed_var_bound_iff [] n).mp
          use (.ty (Ty.mk m))
  )
  simp at h_sub_alpha_noop
  simp [h_sub_alpha_noop] at h
  exact h

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
