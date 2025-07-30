import Mathlib.Tactic

def TyU := Type
abbrev Context := List

inductive Ty {σ : Type} where
  | base  : σ  → Ty
  | arrow : @Ty σ → @Ty σ → Ty

open Ty

inductive Expr {α : Type} {σ : Type} {f_ty : α → Option σ} where
  | abstraction : @Ty σ  → Expr → Expr
  | var         : ℕ      → Expr
  | app         : Expr   → Expr → Expr
  | const       : α      → Expr

open Expr

def map_indices_free {α : Type} {σ : Type} {f_ty : α → Option σ} (n_binders : ℕ) (f : ℕ → ℕ) : @Expr α σ f_ty → @Expr α σ f_ty
  | abstraction e_ty body => abstraction e_ty (map_indices_free n_binders.succ f body)
  -- if bound, don't touch this
  | v@(var n) => if n ≥ n_binders then var (f n) else v
  | app lhs rhs => app (map_indices_free n_binders f lhs) (map_indices_free n_binders f rhs)
  | c@(const _) => c

-- A couple bugs with debrujin indexing noticed. Fixed those.
-- Namely
--
-- When substituting an abstraction inside an abstraction, its free debrujin indices
-- should be incremented
def substitute {α : Type} {σ : Type} {f_ty : α → Option σ} (with_expr : @Expr α σ f_ty) : @Expr α σ f_ty → @Expr α σ f_ty
  | (abstraction bind_ty body) =>
    let with_expr' := map_indices_free 0 (Nat.succ .) with_expr

    abstraction bind_ty (substitute with_expr' body)
  | var 0 => with_expr
  | var n => var $ n - 1
  | app lhs rhs =>
    app (substitute with_expr lhs) (substitute with_expr rhs)
  | c@(const _) => c

-- The size of the type tree will strictly decrease
-- it literally cannot get bigger
-- This is how we do structural recursion
def eval_once {α : Type} {σ : Type} {f_ty : α → Option σ} (ctx : Context $ @Ty σ) : @Expr α σ f_ty → (Context $ @Ty σ) × @Expr α σ f_ty
  | app (abstraction bind_ty body) rhs =>
    ⟨bind_ty::ctx, substitute rhs body⟩
  | app lhs rhs =>
    ⟨ctx, app (eval_once ctx lhs).2 rhs⟩
  | x => ⟨ctx, x⟩

def valid_typing_judgements {α : Type} {σ : Type} {f_ty : α → Option σ} (ctx : Context $ @Ty σ) : @Expr α σ f_ty → Set (@Ty σ)
  | var n =>
    { t | ctx[n]? = some t }
  | const v => { t |
    match t with
      | base t => f_ty v = some t
      | _ => false }
  | app lhs rhs =>
    { t | ∃ ty_lhs ty_rhs, ty_rhs ∈ valid_typing_judgements ctx rhs ∧ ty_lhs ∈ valid_typing_judgements ctx lhs ∧ ty_lhs = arrow ty_rhs t }
  | abstraction bind_ty body =>
    { t | ∃ body_ty, (body_ty : @Ty σ) ∈ valid_typing_judgements ctx body ∧ t = arrow bind_ty body_ty }

inductive valid_typing_judgement {α : Type} {σ : Type} {f_ty : α → Option σ} (ctx : Context $ @Ty σ) : @Expr α σ f_ty → @Ty σ → Prop
  | const v e t (h : e = const v) : some t = (f_ty v).map (Ty.base .) → valid_typing_judgement ctx e t
  | var n e t (h : e = var n) : ctx[n]? = some t → valid_typing_judgement ctx e t
  | app lhs rhs ty_rhs e (t : @Ty σ) (h : e = app lhs rhs) : valid_typing_judgement ctx lhs (arrow ty_rhs t) → valid_typing_judgement ctx rhs ty_rhs → valid_judgement (app lhs rhs) t

inductive beta_normal {α : Type} {σ : Type} {f_ty : α → Option σ} : Context (@Ty σ) → Expr → Prop
  | trivial ctx e   : @eval_once α σ f_ty ctx e = ⟨ctx, e⟩                → beta_normal ctx e
  | hard ctx e      : beta_normal (eval_once ctx e).1 (eval_once ctx e).2 → beta_normal ctx e

inductive beta_eq {α : Type} {σ : Type} {f_ty : α → Option σ} : Context (@Ty σ) → @Expr α σ f_ty → @Expr α σ f_ty → Prop
  | trivial (_ : Context (@Ty σ))   e₁ e₂    : e₁ = e₂                                      → beta_eq ctx e₁ e₂
  | right   ctx e₁ e₂    : e₁ ≠ e₂  → beta_eq (eval_once ctx e₂).1 e₁ (eval_once ctx e₂).2 → beta_eq ctx e₁ e₂
  | left    ctx e₁ e₂    : e₁ ≠ e₂  → beta_eq (eval_once ctx e₁).1 (eval_once ctx e₁).2 e₂ → beta_eq ctx e₁ e₂

inductive is_strongly_normalizing {α : Type} {σ : Type} {f_ty : α → Option σ} : Context (@Ty σ) → @Expr α σ f_ty → Prop
  | trivial (ctx : Context Ty) (e : Expr) : eval_once ctx e = ⟨ctx, e⟩                                      → is_strongly_normalizing ctx e
  | hard    (ctx : Context Ty) (e : Expr) : is_strongly_normalizing (eval_once ctx e).1 (eval_once ctx e).2 → is_strongly_normalizing ctx e

lemma eval_once_noop_not_app {α : Type} {σ : Type} {f_ty : α → Option σ} (ctx : Context Ty) (e : @Expr α σ f_ty) (h_not_app : match e with | app _ _ => false | _ => true) : eval_once ctx e = ⟨ctx, e⟩ := by
  match e with
    | var _ =>
      unfold eval_once
      rfl
    | app _ _ =>
      contradiction
    | abstraction _ _ =>
      unfold eval_once
      rfl
    | const _ =>
      unfold eval_once
      rfl

lemma eval_once_noop_judgement_holds {α : Type} {σ : Type} {f_ty : α → Option σ} (ctx : Context Ty) (e : @Expr α σ f_ty) (h_not_app : match e with | app _ _ => false | _ => true) : ∀ t, t ∈ @valid_typing_judgements α σ f_ty ctx e → t ∈ valid_typing_judgements (eval_once ctx e).1 (eval_once ctx e).2 := by
  match h : e with
    | var _ =>
      simp [eval_once_noop_not_app]
    | app _ _ =>
      contradiction
    | abstraction _ _ =>
      simp [eval_once_noop_not_app]
    | const _ =>
      simp [eval_once_noop_not_app]

lemma eval_abstr_imp_t_in_context {α : Type} {σ : Type} {f_ty : α → Option σ} (ctx : Context $ @Ty σ) (e : @Expr α σ f_ty) (h_is_abstraction : match e with | abstraction _ _ => true | _ => false) : ∀ (arg : @Expr α σ f_ty) t_rhs t_body, (arrow t_rhs t_body) ∈ valid_typing_judgements ctx e → t_rhs ∈ valid_typing_judgements ctx arg → (eval_once ctx (app e arg)).1[0]? = some t_rhs := by
  intro arg t_rhs t_body h_t_e h_t_arg
  unfold eval_once
  unfold valid_typing_judgements at h_t_e
  simp at h_t_e
  match h : e with
    | abstraction _ _ =>
      simp_all
    | var n =>
      simp_all
    | const _ =>
      simp_all
    | app lhs rhs =>
      simp_all

lemma eval_once_judgement_holds {α : Type} {σ : Type} {f_ty : α → Option σ} (ctx : Context $ @Ty σ) : ∀ e t, t ∈ @valid_typing_judgements α σ f_ty ctx e → t ∈ valid_typing_judgements (eval_once ctx e).1 (eval_once ctx e).2
  | e, t, h_t =>
    match h : e with
      | var n =>
        eval_once_noop_judgement_holds ctx (var n) (by simp_all) t h_t
      | app lhs rhs => by
        -- Hard case:
        -- we know that given t is a valid typing judgement,
        -- the type of the lhs is arrow rhs -> t
        -- and the type of the entire expression is the type of body
        unfold valid_typing_judgements at h_t
        simp at h_t
        have ⟨ty_lhs, ty_rhs, ⟨h_ty_rhs, h_t_lhs, h_t'⟩⟩ := h_t
        match h₁ : lhs with
          | a@(abstraction bind_ty body) =>
            -- Evaluation returns the body. We know that the body must be of type t with all vars substituted under the new context
            have h_ctx :=  eval_abstr_imp_t_in_context ctx a (by simp_all) rhs ty_rhs t (by simp_all) (by simp_all)
            
            sorry
          | var n =>
            unfold eval_once
            simp
            unfold eval_once
            unfold valid_typing_judgements
            simp
            exact h_t
          | const _ =>
            unfold eval_once
            simp
            unfold eval_once
            unfold valid_typing_judgements
            simp
            exact h_t
          | app _ _ =>
            sorry
      | abstraction bind_ty body=>
        eval_once_noop_judgement_holds ctx (abstraction bind_ty body) (by simp_all) t h_t
      | const e =>
        eval_once_noop_judgement_holds ctx (const e) (by simp_all) t h_t
