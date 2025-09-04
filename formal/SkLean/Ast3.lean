import Mathlib.Tactic
import Lean

namespace Ast

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | arr  : Expr
  | prp  : Expr
  | hole : Expr
  | ty   : ℕ    → Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr, Lean.ToExpr

inductive ExprBox (e : Ast.Expr) where
  | mk : ExprBox e

declare_syntax_cat skmexpr
syntax "K"                     : skmexpr
syntax "S"                     : skmexpr
syntax "M"                     : skmexpr
syntax "Prp"                   : skmexpr
syntax "Ty" term               : skmexpr
syntax "Typ" num               : skmexpr
syntax "#~>"                   : skmexpr
syntax "_"                     : skmexpr
syntax skmexpr "~>" skmexpr    : skmexpr
syntax skmexpr "!~>" skmexpr   : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax ident                   : skmexpr
syntax "#" term                : skmexpr
syntax "(" skmexpr ")"         : skmexpr

syntax " ⟪ " skmexpr " ⟫ "     : term
syntax "SKM[ " skmexpr " ] "   : term

macro_rules
  | `(SKM[ $e:skmexpr ])  => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K ⟫)                           => `(Expr.k)
  | `(⟪ S ⟫)                           => `(Expr.s)
  | `(⟪ M ⟫)                           => `(Expr.m)
  | `(⟪ Prp ⟫)                         => `(Expr.prp)
  | `(⟪ Ty $n:term ⟫)                  => `(Expr.ty $n)
  | `(⟪ Typ $n:num ⟫)                  => `(Expr.ty $n)
  | `(⟪ _ ⟫)                           => `(Expr.hole)
  | `(⟪ #~> ⟫)                         => `(Expr.arr)
  | `(⟪ $e₁:skmexpr !~> $e₂:skmexpr ⟫) => `(SKM[$e₁ ~> (((K (Ty 0)) $e₁) $e₂)])
  | `(⟪ $e₁:skmexpr ~> $e₂:skmexpr ⟫)  => `(Expr.call (Expr.call Expr.arr ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)   => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

namespace Expr

def toStringImpl (e : Expr) : String :=
  match e with
  | SKM[S]    => "S"
  | SKM[K]    => "K"
  | SKM[M]    => "M"
  | SKM[_]    => "_"
  | SKM[#~>]  => "→"
  | SKM[Ty n] => s!"Type {n}"
  | SKM[Prp]  => "Prop"
  | SKM[(t_in ~> (((K (Ty 0)) t_in') t_out))] =>
    if t_in' == t_in then
      s!"({t_in.toStringImpl} !→ {t_out.toStringImpl})"
    else
      s!"({t_in.toStringImpl} → {t_out.toStringImpl})"
  | SKM[(t_in ~> t_out)] => s!"({t_in.toStringImpl} → {t_out.toStringImpl})"
  | SKM[(lhs rhs)] => s!"({lhs.toStringImpl} {rhs.toStringImpl})"

instance : ToString Expr where
  toString := toStringImpl

def fromExpr (e : Lean.Expr) : Option Expr :=
  match e with
  | .const `Expr.hole [] => pure SKM[_]
  | .const `Expr.k []    => pure SKM[K]
  | .const `Expr.s []    => pure SKM[S]
  | .const `Expr.m []    => pure SKM[M]
  | .const `Expr.arr [] => pure SKM[#~>]
  | .sort .zero => pure SKM[Prp]
  | .sort n => pure SKM[Ty n.depth.pred]
  | .app (.app (.const `Expr.call []) lhs) rhs => do
    let lhs' ← fromExpr lhs
    let rhs' ← fromExpr rhs
    pure SKM[(lhs' rhs')]
  | _ => none

def mk_s_type (t_α α β γ : Ast.Expr) : Ast.Expr :=
  SKM[(α !~> β ~> (((((S _) _) β) (((K ((M #~>) γ)) β) (#~> γ))) ((((S t_α) β) γ) α)))]

end Expr

end Ast
