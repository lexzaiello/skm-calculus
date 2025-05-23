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
def eval_once {α : Type} {σ : Type} {f_ty : α → Option σ} : @Expr α σ f_ty → @Expr α σ f_ty
  | app (abstraction _ body) rhs =>
    substitute rhs body
  | app lhs rhs =>
    app (eval_once lhs) rhs
  | x => x

def valid_typing_judgements {α : Type} {σ : Type} {f_ty : α → Option σ} (ctx : Context $ @Ty σ) : @Expr α σ f_ty → Set (@Ty σ)
  | var n =>
    { t | ctx[n]? = some t }
  | const v => { t |
    match t with
      | base t => f_ty v = some t
      | _ => false }
  | app lhs rhs =>
    { t | ∃ ty_lhs ty_rhs, ty_rhs ∈ valid_typing_judgements ctx rhs → ty_lhs ∈ valid_typing_judgements ctx lhs → ty_lhs = arrow ty_rhs t }
  | abstraction bind_ty body =>
    { t | ∃ body_ty, (body_ty : @Ty σ) ∈ valid_typing_judgements ctx body → t = arrow bind_ty body_ty }

