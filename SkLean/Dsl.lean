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

def to_sk_expr (names : List String) : NamedSkExpr → SkExpr
  | .k => .k
  | .s => .s
  | .prp => .prp
  | .ty n => .ty n
  | .call lhs rhs => .call (to_sk_expr names lhs) (to_sk_expr names rhs)
  | .var name => .var $ ⟨(names.findIdx? (. = name)).getD 0⟩
  | .fall name bind_ty body => .fall
      (to_sk_expr (name :: names) bind_ty)
      (to_sk_expr (name :: names) body)

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
  | `(⟪ ($e₁:skexpr $e₂:skexpr )⟫) => `(NamedSkExpr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

syntax "SK[ " skexpr " ] " : term

macro_rules
  | `(SK[ $e:skexpr ]) => `(NamedSkExpr.to_sk_expr [] ⟪ $e ⟫)

#eval SK[K]
#eval SK[S]
#eval SK[((K K) K)]
