import SkLean.Ast

open Ast
open Expr

namespace Dsl

declare_syntax_cat skmexpr
declare_syntax_cat atom
declare_syntax_cat judgment
declare_syntax_cat operator
declare_syntax_cat app

syntax "universe" : operator

syntax "S"             : atom
syntax "K"             : atom
syntax "M"             : atom
syntax "#~>"            : atom
syntax "#->"             : atom
syntax "<-#"             : atom
syntax "<~#"            : atom
syntax "Prop"          : atom
syntax "Type"          : atom
syntax "(" skmexpr ")" : atom
syntax operator        : atom
syntax judgment        : atom
syntax "#" term        : atom
syntax "@" atom        : atom

syntax app atom : app
syntax atom     : app

syntax app           : skmexpr

syntax "⟪" skmexpr "⟫" : term
syntax "⟪₀" atom "⟫"   : term
syntax "⟪₁" app "⟫"    : term

macro_rules
  | `(⟪₀ ($e:skmexpr)⟫) => `(⟪ $e ⟫)
  | `(⟪ $e:atom ⟫) => `(⟪₀ $e ⟫)
  | `(⟪ $e:app ⟫) => `(⟪₁ $e ⟫)
  | `(⟪₁ $e:atom ⟫) => `(⟪₀ $e ⟫)
  | `(⟪₀ #~> ⟫) => `(Expr.pi)
  | `(⟪₀ <~# ⟫) => `(Expr.pi')
  | `(⟪₀ #-> ⟫)  => `(Expr.imp)
  | `(⟪₀ <-# ⟫)  => `(Expr.imp')
  | `(⟪₀ M ⟫)  => `(Expr.m)
  | `(⟪₀ Prop ⟫)  => `(Expr.prp)
  | `(⟪₀ #$t:term ⟫) => `($t)
  | `(⟪₁ Type #$n:term ⟫) => `(Expr.ty $n)
  | `(⟪₁ universe $e:atom ⟫)      => `(Expr.max_universe ⟪₀ $e ⟫)
  | `(⟪₁ @S $m:atom $n:atom $o:atom ⟫) => `(Expr.s ⟪₀ $m⟫ ⟪₀ $n⟫ ⟪₀ $o⟫)
  | `(⟪₁ @K $m:atom $n:atom ⟫) => `(Expr.k ⟪₀ $m⟫ ⟪₀ $n⟫)
  | `(⟪₁ S $m:atom $n:atom $o:atom ⟫) => `(⟪ @S (universe $m) (universe $n) (universe $o) $m $n $o ⟫)
  | `(⟪₁ K $m:atom $n:atom ⟫) => `(⟪ @K (universe $m) (universe $n) $m $n ⟫)
  | `(⟪₁ $e₁:app $e₂:atom ⟫) => `(Expr.app ⟪₁ $e₁⟫ ⟪₀ $e₂⟫)

end Dsl

#eval ⟪ M M ⟫
#eval ⟪ Type #0 ⟫



