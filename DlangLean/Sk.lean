import Mathlib.Tactic

inductive SkExpr where
  | k    : SkExpr
  | s    : SkExpr
  | call : SkExpr → SkExpr → SkExpr
  | fall : SkExpr → SkExpr → SkExpr
  | var  : ℕ → SkExpr
  | ty   : ℕ → SkExpr
  | prp : SkExpr

open SkExpr

def substitute (n : ℕ) (with_expr : SkExpr): SkExpr → SkExpr
  | prp => ty 0
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

abbrev ty_k := fall (SkExpr.var 1) (
  fall (SkExpr.var 1) (fall (SkExpr.var 3) (fall (SkExpr.var 3) (SkExpr.var 4))))

def imp := fall

infixr:65 " ~> " => imp

def specialize_ty_k (α β : SkExpr) := α ~> β ~> α
def specialize_ty_s (α β γ : SkExpr) := (α ~> β ~> γ) ~> (α ~> β) ~> α ~> γ

--               α                 β                 γ               x : α → β → γ                                            y : α → β                             z : α             γ
abbrev ty_s := (SkExpr.var 1) ~> (SkExpr.var 1) ~> (SkExpr.var 1) ~> ((SkExpr.var 4) ~> (SkExpr.var 4) ~> (SkExpr.var 4)) ~> ((SkExpr.var 5) ~> (SkExpr.var 4)) ~> (SkExpr.var 6) ~> (SkExpr.var 4)

def eval_once : SkExpr → SkExpr
  | k => k
  | s => s
  | call (call k x) _ => x
  | call (call (call s x) y) z => call (call x z) (call y z)
  | x => x

inductive beta_eq : SkExpr → SkExpr → Prop
  | trivial e₁ e₂    : e₁ = e₂ → beta_eq e₁ e₂
  | hard    e₁ e₂    : beta_eq e₁ (eval_once e₂) → beta_eq e₁ e₂
  | symm    e₁ e₂    : beta_eq e₂ e₁ → beta_eq e₁ e₂
  | trans   e₁ e₂ e₃ : beta_eq e₁ e₂ → beta_eq e₂ e₃ → beta_eq e₁ e₃

inductive valid_judgement : SkExpr → SkExpr → Prop
  | k e t (h_is_k : match e with | SkExpr.k => true | _ => false) :
    -- K α : ∀ β.∀ (x : α).∀ (y : β).α
    t = ty_k → valid_judgement e t
  | s e t (h_is_s : match e with | SkExpr.s => true | _ => false) :
    -- ∀ α β γ (x : α → β → γ) (y : α → β) (z : α), γ
    t = ty_s → valid_judgement e t
  | call e t (lhs : SkExpr) (rhs : SkExpr) (t_lhs : SkExpr) (t_rhs : SkExpr) (h_is_call : match e with | call lhs' rhs' => lhs' = lhs ∧ rhs' = rhs | _ => false) :
    valid_judgement lhs t_lhs → valid_judgement rhs t_rhs → t = body (substitute 0 rhs t_lhs) → valid_judgement e t
  | fall e t bind_ty body t_body (h_is_fall : match e with | fall _ _ => true | _ => false) :
    valid_judgement body t_body →
    e = fall bind_ty body →
    t = t_body → valid_judgement e t
  | obvious e t : (match e with | ty n => t = ty n.succ | prp => t = ty 0 | _ => false) → valid_judgement e t
  | beta_eq e e₂ t : beta_eq e e₂ → valid_judgement e₂ t → valid_judgement e t

inductive sn : SkExpr → Prop
  | trivial e : eval_once e = e    → sn e
  | hard    e : (sn ∘ eval_once) e → sn e

inductive in_r : SkExpr → SkExpr → Prop
  -- K α β is in r if all of its one-step reduxes are in R
  | k t e α β (h_t : t = (specialize_ty_k α β)) : ∀ arg₁ arg₂,
    valid_judgement t e →
    in_r α arg₁ →
    in_r (eval_once (call (call (call (call k α) β) arg₁) arg₂)) α →
    in_r t e
  | s t e α β γ (h_t : t = (specialize_ty_s α β γ)) : ∀ arg₁ arg₂ arg₃,
    valid_judgement t e →
    in_r 
  | obvious t e (h_is_obv : match e with | ty _ => true | fall _ _ => true | _ => false) : valid_judgement e t → in_r t e

example : eval_once (call (call k k) k) = k := by
  unfold eval_once
  simp

example : (eval_once ∘ eval_once) (call (call (call s k) k) k) = k := by
  unfold eval_once
  simp

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

-- S prp prp prp (k prp prp) (

-- K α β : ∀ (x : α).∀ (y : β).α
example : valid_judgement (call (call k (ty 1)) (ty 2)) (fall (ty 1) (fall (ty 2) (ty 1))) := by
  apply (valid_judgement.call
    -- e
    (call (call k (ty 1)) (ty 2))
    -- t
    (fall (ty 1) (fall (ty 2) (ty 1)))
    -- lhs
    (call k (ty 1))
    -- rhs
    (ty 2)
    -- t_lhs
    (fall (var 1) (fall (ty 1) (fall (var 3) (ty 1))))
    -- t_rhs
    (ty 3)
    (by simp)
  )
  apply (valid_judgement.call
    (k.call (ty 1))
    ((var 1).fall ((ty 1).fall ((var 3).fall (ty 1))))
    k
    (ty 1)
    (fall (SkExpr.var 1) (
          fall (SkExpr.var 1) (fall (SkExpr.var 3) (fall (SkExpr.var 3) (SkExpr.var 4)))))
    (ty 2)
    (by simp)
  )
  simp [valid_judgement.k]
  simp [valid_judgement.obvious]
  repeat unfold substitute
  unfold body
  simp
  simp [valid_judgement.obvious]
  unfold body
  repeat unfold substitute
  simp

