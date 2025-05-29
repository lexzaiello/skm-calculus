import SkLean.Ast
import SkLean.Dsl
import SkLean.Typing

open SkExpr

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
