import SkLean.Ast
import SkLean.Dsl
import Mathlib.Tactic

open SkExpr

abbrev Ctx := List SkExpr

def ty_k := SK[∀ α : Type 0, ∀ β : Type 0, #α → #β → #α]
def ty_s := SK[∀ α : Type 0, ∀ β : Type 0, ∀ γ : Type 0, (#α → #β → #γ) → (#α → #β) → #α → #γ]

partial def type_of_unsafe (ctx : Ctx) : SkExpr → Option SkExpr
  | ty n => some $ ty n.succ
  | var n => ctx[n.toNat - 1]?
  | prp => ty 0
  | k => ty_k
  | s => ty_s
  | fall bind_ty body => type_of_unsafe (bind_ty :: ctx) body
  | call lhs rhs => do
    let t_lhs <- type_of_unsafe ctx lhs
    pure $ (t_lhs.substitute ⟨0⟩ rhs).body

#eval ty_k
#eval ty_k.substitute ⟨0⟩ ty_k
#eval ty_s
#eval (type_of_unsafe [] SK[K]) == ty_k
#eval (type_of_unsafe [] SK[K])
#eval (type_of_unsafe [] SK[(K ty_k)]) == SK[∀ β : Type 0, ∀ x : ty_k, ∀ y : #β, ty_k]
#eval (type_of_unsafe [] SK[((K ty_k) ty_k)]) == SK[∀ x : ty_k, ∀ y : ty_k, ty_k]

inductive beta_eq : SkExpr → SkExpr → Prop
  | trivial e₁ e₂    : e₁ = e₂ → beta_eq e₁ e₂
  | hard    e₁ e₂    : beta_eq e₁ (eval_once e₂) → beta_eq e₁ e₂
  | symm    e₁ e₂    : beta_eq e₂ e₁ → beta_eq e₁ e₂
  | trans   e₁ e₂ e₃ : beta_eq e₁ e₂ → beta_eq e₂ e₃ → beta_eq e₁ e₃

inductive valid_judgement : Ctx → SkExpr → SkExpr → Prop
  | k ctx e t (h_is_k : match e with | SkExpr.k => true | _ => false) :
    t = ty_k → valid_judgement ctx e t
  | s ctx e t (h_is_s : match e with | SkExpr.s => true | _ => false) :
    t = ty_s → valid_judgement ctx e t
  | call ctx e t (lhs : SkExpr) (rhs : SkExpr) (t_lhs : SkExpr) (t_rhs : SkExpr) (h_is_call : match e with | call lhs' rhs' => lhs' = lhs ∧ rhs' = rhs | _ => false) :
    valid_judgement ctx lhs t_lhs → valid_judgement ctx rhs t_rhs → t = (t_lhs.substitute ⟨0⟩ rhs).body → valid_judgement ctx e t
  | fall ctx e t bind_ty body t_body (h_is_fall : match e with | fall _ _ => true | _ => false) :
    valid_judgement (bind_ty :: ctx) body t_body →
    e = fall bind_ty body →
    t = t_body → valid_judgement ctx e t
  | obvious ctx e t : (match e with | ty n => t = ty n.succ | prp => t = ty 0 | var ⟨n + 1⟩ => ctx[n]? = some t | _ => false) → valid_judgement ctx e t
  | beta_eq ctx e e₂ t : beta_eq e e₂ → valid_judgement ctx e₂ t → valid_judgement ctx e t

inductive sn : SkExpr → Prop
  | trivial e : eval_once e = e    → sn e
  | hard    e : (sn ∘ eval_once) e → sn e

inductive in_r : Ctx → SkExpr → SkExpr → Prop
  | k ctx e t α β (h_t : t = SK[α → β → α]) : ∀ arg₁ arg₂,
    valid_judgement ctx e t →
    in_r ctx α arg₁ →
    in_r ctx (eval_once (call (call (call (call k α) β) arg₁) arg₂)) α →
    in_r ctx e t
  | s ctx e t (α : SkExpr) (β : SkExpr) (γ : SkExpr) (h_t : t = SK[(α → β → γ) → (α → β) → α → γ]) : ∀ arg₁ arg₂ arg₃, sorry → in_r ctx e t
  | obvious ctx e t (h_is_obv : match e with | ty _ => true | fall _ _ => true | _ => false) : valid_judgement ctx e t → in_r ctx e t

example : eval_once SK[((((K k_ty) k_ty) K) K)]  = k := by
  unfold eval_once
  repeat unfold NamedSkExpr.to_sk_expr
  simp

-- SKKK = K K (K K) = K
example :
  let x := SK[((K ty_k) (∀ y : Type 0, ty_k))]
  let y := SK[((K ty_k) (Type 0))]
  let z := SK[K]
  let ty_x := SK[∀ x : ty_k, ∀ y : (∀ y : Type 0, ty_k), ty_k]
  let ty_y := SK[∀ x : ty_k, ∀ y : Type 0, ty_k]
  let ty_z := ty_k
  beta_eq SK[((((((S ty_x) ty_y) ty_z) x) y) z)] SK[K] := by
  repeat unfold NamedSkExpr.to_sk_expr at *
  simp_all
  apply beta_eq.symm
  apply beta_eq.hard
  unfold eval_once
  simp
  apply beta_eq.hard
  unfold eval_once
  simp
  exact beta_eq.trivial k k rfl
