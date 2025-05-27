import Mathlib.Tactic

inductive SkExpr where
  | k    : SkExpr
  | s    : SkExpr
  | call : SkExpr → SkExpr → SkExpr
  | fall : SkExpr → SkExpr → SkExpr
  | var  : ℕ → SkExpr
  | ty   : ℕ → SkExpr

open SkExpr

abbrev Context := List SkExpr

inductive valid_judgement (ctx : Context) : SkExpr → SkExpr → Prop
  | k e t (h_is_k : match e with | SkExpr.k => true | _ => false) :
    -- ∀ α β (x : α) (y : β), α
    ∀ n m,
      t = fall (SkExpr.ty 0) (
        fall (SkExpr.ty 0) (
          fall (SkExpr.var n) (
            fall (SkExpr.var m) (SkExpr.var 3)))) → valid_judgement ctx e t
  | s e t (h_is_s : match e with | SkExpr.s => true | _ => false) :
    -- ∀ α β γ (x : α → β → γ) (y : α → β) (z : α), γ
    ∀ n m o,
      t = fall (SkExpr.ty n) (
        fall (SkExpr.ty m) (
          fall (SkExpr.ty o) (
          fall (SkExpr.var 1) (
            fall (SkExpr.var 1) (
              fall (SkExpr.var 1) (
                SkExpr.var 3)))))) → valid_judgement ctx e t
  | call e t (lhs : SkExpr) (rhs : SkExpr) (t_rhs : SkExpr) (h_is_call : match e with | call _ _ => true | _ => false) :
    valid_judgement ctx rhs t_rhs → valid_judgement ctx lhs (fall t_rhs t) → valid_judgement ctx e t
  | fall e t bind_ty body t_body (h_is_fall : match e with | fall _ _ => true | _ => false) :
    valid_judgement ctx body t_body →
    e = fall bind_ty body →
    t = t_body → valid_judgement ctx e t
  | obvious e t : (match e with | ty n => t = ty (Nat.succ n) | var n => ctx[n]? = t | _ => false) → valid_judgement ctx e t


