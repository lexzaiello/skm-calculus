import SkLean.Ast

inductive NamedSkExpr where
  | k    : NamedSkExpr
  | s    : NamedSkExpr
  | prp  : NamedSkExpr
  | ty   : ℕ      → NamedSkExpr
  | fall : String → NamedSkExpr → NamedSkExpr → NamedSkExpr
  | call : NamedSkExpr → NamedSkExpr → NamedSkExpr
  | var  : String → NamedSkExpr

namespace NamedSkExpr

def to_sk_expr (names : List String) : NamedSkExpr → Option SkExpr
  | .k => some .k
  | .s => some .s
  | .prp => some .prp
  | .ty n => some $ .ty n
  | .call lhs rhs => do
    some $ .call (← (to_sk_expr names lhs)) (← (to_sk_expr names rhs))
  | .var name => do
    some $ .var ⟨← names.findIdx? (. = name)⟩
  | .fall name bind_ty body => do
    some $ .fall
      (← (to_sk_expr (name :: names) bind_ty))
      (← (to_sk_expr (name :: names) body))

end NamedSkExpr

declare_syntax_cat skexpr
syntax "K"                                         : skexpr
syntax "S"                                         : skexpr
syntax "prop"                                      : skexpr
syntax "ty" num                                    : skexpr
syntax "∀"  "(" str ":" skexpr ")",+ "." skexpr    : skexpr
syntax "(" skexpr skexpr ")"                       : skexpr
syntax str                                         : skexpr

syntax " ⟪ " skexpr " ⟫ " : term

macro_rules
  | `(⟪ K ⟫)              => `(NamedSkExpr.k)
  | `(⟪ S ⟫)              => `(NamedSkExpr.s)
  | `(⟪ prop ⟫)           => `(NamedSkExpr.prp)
  | `(⟪ ty $n:num ⟫)      => `(NamedSkExpr.ty $n)
  | `(⟪ $var:str ⟫)       => `(NamedSkExpr.var $var)
  | `(⟪ ∀ ($var:str : $e_ty:skexpr).$body:skexpr ⟫) => `(NamedSkExpr.fall $var ⟪ $e_ty ⟫ ⟪ $body ⟫)
  | `(⟪ $e₁:skexpr ⟫ ⟪ $e₂:skexpr ⟫) => `(NamedSkExpr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

