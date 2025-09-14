import SkLean.Ast

open Ast
open Expr

namespace Dsl

declare_syntax_cat skmexpr
declare_syntax_cat atom
declare_syntax_cat judgment
declare_syntax_cat operator
declare_syntax_cat app
declare_syntax_cat arrow

syntax "S"             : atom
syntax "K"             : atom
syntax "M"             : atom
syntax "T"             : atom
syntax "->"            : atom
syntax "<-"            : atom
syntax "Type"          : atom
syntax "Syntax"        : atom
syntax "(" skmexpr ")" : atom
syntax operator        : atom
syntax judgment        : atom
syntax "#" term        : atom
syntax "@" atom        : atom

syntax app atom : app
syntax atom     : app

syntax atom "→" arrow : arrow
syntax arrow "←" atom : arrow
syntax atom           : arrow

syntax arrow         : skmexpr
syntax app           : skmexpr

syntax "⟪" skmexpr "⟫" : term
syntax "⟪₀" atom "⟫"   : term
syntax "⟪₁" app "⟫"    : term
syntax "⟪₂" arrow "⟫"  : term

macro_rules
  | `(⟪₀ T ⟫)      => `(Expr.t)
  | `(⟪₀ Type ⟫)   => `(Expr.ty)
  | `(⟪₀ Syntax ⟫) => `(Expr.stx)
  | `(⟪ $e:arrow ⟫) => `(⟪₂ $e ⟫)
  | `(⟪₂ ($e:skmexpr) ⟫) => `(⟪ $e ⟫)
  | `(⟪₂ $e:atom ⟫) => `(⟪₀ $e ⟫)
  | `(⟪₂ $t_in:atom → $t_out:arrow ⟫) => `(Expr.app ⟪₁ (->) $t_in ⟫ ⟪₂ $t_out ⟫)
  | `(⟪₂ $t_out:arrow ← $t_in:atom ⟫) => `(⟪₂ $t_in:atom → $t_out:arrow ⟫)
  | `(⟪₀ ($e:skmexpr)⟫) => `(⟪ $e ⟫)
  | `(⟪ $e:atom ⟫) => `(⟪₀ $e ⟫)
  | `(⟪ $e:app ⟫) => `(⟪₁ $e ⟫)
  | `(⟪₁ $e:atom ⟫) => `(⟪₀ $e ⟫)
  | `(⟪₀ -> ⟫) => `(Expr.imp)
  | `(⟪₀ <- ⟫) => `(Expr.imp')
  | `(⟪₀ M ⟫)  => `(Expr.m)
  | `(⟪₀ K ⟫)  => `(Expr.k)
  | `(⟪₀ S ⟫)  => `(Expr.s)
  | `(⟪₀ #$t:term ⟫) => `($t)
  | `(⟪₁ $e₁:app $e₂:atom ⟫) => `(Expr.app ⟪₁ $e₁⟫ ⟪₀ $e₂⟫)

end Dsl

#eval ⟪ M → K → M ⟫
