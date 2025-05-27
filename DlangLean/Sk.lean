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

def map_indices_free (n_binders : ℕ) (f : ℕ → ℕ) : SkExpr → SkExpr
  | fall e_ty body => fall (map_indices_free n_binders.succ f e_ty) (map_indices_free n_binders.succ f body)
  | t@(ty _) => t
  -- if bound, don't touch this
  | v@(var n) => if n ≥ n_binders then var (f n) else v
  | x => x

def substitute (with_expr : SkExpr) : SkExpr → SkExpr
  | fall bind_ty body =>
    let with_expr' := map_indices_free 0 (Nat.succ .) with_expr

    fall (substitute with_expr' bind_ty) (substitute with_expr' body)
  | t@(ty _) => t
  | var 0 => with_expr
  | var n => var $ n - 1
  | x => x

inductive valid_judgement : Context → SkExpr → SkExpr → Prop
  | k e t (h_is_k : match e with | SkExpr.k => true | _ => false) n m :
    -- ∀ α β (x : α) (y : β), α
    t = fall (SkExpr.ty n) (
      fall (SkExpr.ty m) (
        fall (SkExpr.var 0) (
          fall (SkExpr.var 0) (SkExpr.var 3)))) → valid_judgement ctx e t
  | s e t (h_is_s : match e with | SkExpr.s => true | _ => false) n m o :
    -- ∀ α β γ (x : α → β → γ) (y : α → β) (z : α), γ
    t = fall (SkExpr.ty n) (
      fall (SkExpr.ty m) (
        fall (SkExpr.ty o) (
        fall (SkExpr.var 1) (
          fall (SkExpr.var 1) (
            fall (SkExpr.var 1) (
              SkExpr.var 3)))))) → valid_judgement ctx e t
  | call e t (lhs : SkExpr) (rhs : SkExpr) (t_rhs : SkExpr) (h_is_call : match e with | call _ _ => true | _ => false) :
    valid_judgement ctx rhs t_rhs → valid_judgement (t_rhs :: ctx) (substitute lhs rhs) (fall t_rhs t) → valid_judgement ctx e t
  | fall e t bind_ty body t_body (h_is_fall : match e with | fall _ _ => true | _ => false) :
    valid_judgement ctx body t_body →
    e = fall bind_ty body →
    t = t_body → valid_judgement ctx e t
  | obvious e t : (match e with | ty n => t = ty (Nat.succ n) | var n => ctx[n]? = t | _ => false) → valid_judgement ctx e t

def eval_once : SkExpr → SkExpr
  | k => k
  | s => s
  | call (call k x) _ => x
  | call (call (call s x) y) z => call (call x z) (call y z)
  | x => x

def bruh := (call (call (call (call k (ty 1)) (ty 1)) (ty 0)) (ty 0))
def is_valid_bruh : valid_judgement [] bruh (ty 1) :=
  valid_judgement.call
    bruh
    (ty 1)
    (call (call (call k (ty 1)) (ty 1)) (ty 0))
    (ty 0)
    (ty 1)
    (by unfold bruh; simp)
    (valid_judgement.obvious
      (ty 0)
      (ty 1)
      (by simp))
    (valid_judgement.call
      (substitute (((k.call (ty 1)).call (ty 1)).call (ty 0)) (ty 0))
      (call (call (call k (ty 1)) (ty 1)) (ty 0))
      ((ty 1).fall (ty 1))
      (call (call k (ty 1)) (ty 1))
      (ty 0)
      (ty 1)
      (by simp)
      (valid_judgement.obvious (ty 0) (ty 1) (by simp))
      (@valid_judgement.call []
        ((k.call (ty 1)).call (ty 1))
        ((ty 1).fall ((ty 1).fall (ty 1)))
        (k.call (ty 1))
        (ty 1)
        (ty 2)
        (by simp_all)
        (valid_judgement.obvious (ty 1) (ty 2) (by simp))
        (@valid_judgement.call
          []
          (k.call (ty 1))
          ((ty 2).fall ((ty 1).fall ((ty 1).fall (ty 1))))
          k
          (ty 1)
          (ty 2)
          (by simp)
          (valid_judgement.obvious (ty 1) (ty 2) (by simp))
          (@valid_judgement.k [] k
            ((ty 2).fall ((ty 2).fall ((var 0).fall ((var 0).fall (var 3)))))
            (by simp)
            2
            2
            rfl
          )
        )
      ))

#eval valid_judgement [] 
