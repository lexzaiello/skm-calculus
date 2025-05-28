import Mathlib.Tactic

inductive SkExpr where
  | k    : SkExpr
  | s    : SkExpr
  | call : SkExpr → SkExpr → SkExpr
  | fall : SkExpr → SkExpr → SkExpr
  | var  : ℕ → SkExpr
  | ty   : ℕ → SkExpr

open SkExpr

def substitute (n : ℕ) (with_expr : SkExpr): SkExpr → SkExpr
  | fall bind_ty body =>
    fall (substitute n.succ with_expr bind_ty) (substitute n.succ with_expr body)
  | t@(ty _) => t
  | var n' => if n == n' then with_expr else var $ n - 1
  | call lhs rhs =>
    call (substitute n with_expr lhs) (substitute n with_expr rhs)
  | k => k
  | s => s

def body : SkExpr → SkExpr
  | fall _ body => body
  | x => x

inductive valid_judgement : SkExpr → SkExpr → Prop
  | k e t (h_is_k : match e with | SkExpr.k => true | _ => false) :
    -- K α : ∀ β.∀ (x : α).∀ (y : β).α
    t = fall (SkExpr.var 1) (
          fall (SkExpr.var 1) (fall (SkExpr.var 3) (fall (SkExpr.var 3) (SkExpr.var 4)))) → valid_judgement e t
  | s e t (h_is_s : match e with | SkExpr.s => true | _ => false) :
    -- ∀ α β γ (x : α → β → γ) (y : α → β) (z : α), γ
    t = fall (SkExpr.var 1) (
          fall (SkExpr.var 1) (fall (SkExpr.var 1) (fall (SkExpr.var 4) (fall (SkExpr.var 4) (SkExpr.var 5))))) → valid_judgement e t
  | call e t (lhs : SkExpr) (rhs : SkExpr) (t_lhs : SkExpr) (t_rhs : SkExpr) (h_is_call : match e with | call lhs' rhs' => lhs' = lhs ∧ rhs' = rhs | _ => false) :
    valid_judgement lhs t_lhs → valid_judgement rhs t_rhs → t = body (substitute 0 rhs t_lhs) → valid_judgement e t
  | fall e t bind_ty body t_body (h_is_fall : match e with | fall _ _ => true | _ => false) :
    valid_judgement body t_body →
    e = fall bind_ty body →
    t = t_body → valid_judgement e t
  | obvious e t : (match e with | ty n => t = ty n.succ | _ => false) → valid_judgement e t

def eval_once : SkExpr → SkExpr
  | k => k
  | s => s
  | call (call k x) _ => x
  | call (call (call s x) y) z => call (call x z) (call y z)
  | x => x

-- K α : ∀ β.∀ (x : α).∀ (y : β).α
example : valid_judgement (call k (ty 1)) (fall (var 1) (fall (ty 1) (fall (var 3) (ty 1)))) := by
  apply (valid_judgement.call
    -- e
    (call k (ty 1))
    -- t
    (fall (var 1) (fall (ty 1) (fall (var 3) (ty 1))))
    -- lhs
    k
    -- rhs
    (ty 1)
    -- t_lhs
    (fall (SkExpr.var 1) (
          fall (SkExpr.var 1) (fall (SkExpr.var 3) (fall (SkExpr.var 3) (SkExpr.var 4)))))
    -- t_rhs
    (ty 2)
    (by simp)
  )
  simp [valid_judgement.k]
  simp [valid_judgement.obvious]
  unfold substitute
  simp
  repeat unfold substitute
  simp
  unfold body
  simp

