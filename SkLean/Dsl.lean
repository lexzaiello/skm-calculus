import SkLean.Ast

inductive NamedSkExpr where
  | k    : NamedSkExpr
  | s    : NamedSkExpr
  | prp  : NamedSkExpr
  | ty   : ℕ      → NamedSkExpr
  | fall : String → NamedSkExpr → NamedSkExpr → NamedSkExpr
  | call : NamedSkExpr → NamedSkExpr → NamedSkExpr
  | var  : String → NamedSkExpr
  | e    : SkExpr → NamedSkExpr

namespace NamedSkExpr

def to_sk_expr (names : List String) : NamedSkExpr → SkExpr
  | .k => .k
  | .e e' => e'
  | .s => .s
  | .prp => .prp
  | .ty n => .ty n
  | .call lhs rhs => .call (to_sk_expr names lhs) (to_sk_expr names rhs)
  | .var name => .var $ ⟨Nat.succ <| (names.findIdx? (. = name)).getD 0⟩
  | .fall name bind_ty body => .fall
      (to_sk_expr (name :: names) bind_ty)
      (to_sk_expr (name :: names) body)

end NamedSkExpr

declare_syntax_cat skexpr
syntax "K"                                         : skexpr
syntax "S"                                         : skexpr
syntax "Prop"                                      : skexpr
syntax "Type" num                                  : skexpr
syntax "∀"  ident ":" skexpr "," skexpr  : skexpr
syntax "(" skexpr skexpr ")"                       : skexpr
syntax "(" skexpr ")"                              : skexpr
syntax ident                                       : skexpr
syntax "#" ident                                       : skexpr
syntax skexpr "→" skexpr                           : skexpr

syntax " ⟪ " skexpr " ⟫ " : term

macro_rules
  | `(⟪ ($e:skexpr) ⟫) => `(⟪ $e ⟫)
  | `(⟪ K ⟫)              => `(NamedSkExpr.k)
  | `(⟪ S ⟫)              => `(NamedSkExpr.s)
  | `(⟪ Prop ⟫)           => `(NamedSkExpr.prp)
  | `(⟪ Type $n:num ⟫)    => `(NamedSkExpr.ty $n)
  | `(⟪ #$var:ident ⟫)       =>
    `(NamedSkExpr.var $(Lean.quote var.getId.toString))
  | `(⟪ $var:ident ⟫)       => `(NamedSkExpr.e $var)
  | `(⟪ $e₁:skexpr → $e₂:skexpr ⟫) => `(⟪ ∀ x : $e₁, $e₂ ⟫)
  | `(⟪ ∀ $var:ident : $e_ty:skexpr , $body:skexpr ⟫) =>
    `(NamedSkExpr.fall $(Lean.quote var.getId.toString) ⟪ $e_ty ⟫ ⟪ $body ⟫)
  | `(⟪ ($e₁:skexpr $e₂:skexpr )⟫) => `(NamedSkExpr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

syntax "SK[ " skexpr " ] " : term

macro_rules
  | `(SK[ $e:skexpr ]) => `(NamedSkExpr.to_sk_expr [] ⟪ $e ⟫)

#eval SK[K]
#eval SK[S]
#eval SK[∀ x : Prop, (∀ y : #x, Prop)]
#eval SK[∀ α : #α, (∀ β : #β, (∀ x : #α, (∀ y : #β, #α)))]
#eval SK[Prop → Prop]
