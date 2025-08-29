import Mathlib.Tactic
import Lean

namespace Ast

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | arr  : Expr
  | ty   : ℕ → Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr, Lean.ToExpr

declare_syntax_cat skmexpr
syntax "K"                     : skmexpr
syntax "S"                     : skmexpr
syntax "M"                     : skmexpr
syntax "#~>"                   : skmexpr
syntax skmexpr "~>" skmexpr    : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax ident                   : skmexpr
syntax "Ty" term               : skmexpr
syntax "#" term                : skmexpr
syntax "(" skmexpr ")"         : skmexpr

syntax " ⟪ " skmexpr " ⟫ "     : term
syntax "SKM[ " skmexpr " ] "   : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K ⟫)                           => `(Expr.k)
  | `(⟪ S ⟫)                           => `(Expr.s)
  | `(⟪ M ⟫)                           => `(Expr.m)
  | `(⟪ Ty $n:term ⟫)                  => `(Expr.ty $n)
  | `(⟪ #~> ⟫)                         => `(Expr.arr)
  | `(⟪ $e₁:skmexpr ~> $e₂:skmexpr ⟫)  => `(Expr.call (Expr.call Expr.arr ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)   => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

namespace Expr

def toStringImpl (e : Expr) : String :=
  match e with
  | SKM[S] => "S"
  | SKM[K] => "K"
  | SKM[M] => "M"
  | SKM[#~>] => "→"
  | SKM[(t_in ~> t_out)] => s!"{t_in.toStringImpl} → {t_out.toStringImpl}"
  | SKM[(lhs rhs)] => s!"({lhs.toStringImpl} {rhs.toStringImpl})"
  | SKM[Ty n] => s!"Type {n}"

instance : ToString Expr where
  toString := toStringImpl

def fromExpr (e : Lean.Expr) : Option Expr :=
  match e with
  | .const `Expr.k [] => pure SKM[K]
  | .const `Expr.s [] => pure SKM[S]
  | .const `Expr.m [] => pure SKM[M]
  | .app (.const `Expr.ty []) (.lit (.natVal n)) => pure SKM[Ty n]
  | .const `Expr.arr [] => pure SKM[#~>]
  | .app (.app (.const `Expr.call []) lhs) rhs => do
    let lhs' ← fromExpr lhs
    let rhs' ← fromExpr rhs
    pure SKM[(lhs' rhs')]
  | _ => none

end Expr

end Ast
