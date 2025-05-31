/-
I define a DSL to convert human-readable input with named variable to De Bruijn indexed AST expressions.
-/

import SkLean.Ast

/-
De Bruijn and "named variable" expresions are mixed in the same tree.
-/

inductive NamedSkExpr where
  | k    : NamedSkExpr
  | s    : NamedSkExpr
  | prp  : NamedSkExpr
  | ty   : ℕ           → NamedSkExpr
  | fall : String      → NamedSkExpr → NamedSkExpr → NamedSkExpr
  | call : NamedSkExpr → NamedSkExpr → NamedSkExpr
  | var  : String      → NamedSkExpr
  | e    : SkExpr      → NamedSkExpr

namespace NamedSkExpr

/-
De Bruijn indices are assigned eagerly based on the location of the nearest bound matching variable.
-/
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

/-
Use like:

SK[K]
SK[(K (Type 0))]
SK[∀ α : Type 0, ∀ β : Type 0, ∀ x : α, ∀ y : β, α]
-/

declare_syntax_cat skexpr
syntax "K"                                         : skexpr
syntax "S"                                         : skexpr
syntax "Prop"                                      : skexpr
syntax "Type" num                                  : skexpr
syntax "Type" ident                                : skexpr
syntax "∀"  ident ":" skexpr "," skexpr  : skexpr
syntax "(" skexpr skexpr ")"                       : skexpr
syntax "(" skexpr ")"                              : skexpr
syntax ident                                       : skexpr
syntax "#" ident                                   : skexpr
syntax skexpr "→" skexpr                           : skexpr

syntax " ⟪ " skexpr " ⟫ " : term

macro_rules
  | `(⟪ ($e:skexpr) ⟫) => `(⟪ $e ⟫)
  | `(⟪ K ⟫)              => `(NamedSkExpr.k)
  | `(⟪ S ⟫)              => `(NamedSkExpr.s)
  | `(⟪ Prop ⟫)           => `(NamedSkExpr.prp)
  | `(⟪ Type $n:num ⟫)    => `(NamedSkExpr.ty $n)
  | `(⟪ Type $v:ident ⟫)    => `(NamedSkExpr.ty $v)
  | `(⟪ #$var:ident ⟫)       =>
    `(NamedSkExpr.var $(Lean.quote var.getId.toString))
  | `(⟪ $var:ident ⟫)       => `(NamedSkExpr.e $var)
  | `(⟪ $e₁:skexpr → $e₂:skexpr ⟫) => `(⟪ ∀ x : $e₁, $e₂ ⟫)
  | `(⟪ ∀ $var:ident : $e_ty:skexpr , $body:skexpr ⟫) =>
    `(NamedSkExpr.fall $(Lean.quote var.getId.toString) (⟪ $e_ty ⟫) (⟪ $body ⟫))
  | `(⟪ ($e₁:skexpr $e₂:skexpr )⟫) => `(NamedSkExpr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

syntax "SK[ " skexpr " ] " : term

macro_rules
  | `(SK[ $e:skexpr ]) => `(NamedSkExpr.to_sk_expr [] ⟪ $e ⟫)

/-
Variables in body position must be prefixed with #.
-/
#eval SK[∀ α : Type 0, ∀ β : Type 0, ∀ x : #α, ∀ y : #β, #α]
