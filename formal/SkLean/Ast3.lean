import Mathlib.Tactic
import Lean

namespace Ast

inductive Expr where
  | k    : ℕ → ℕ → Expr
  | s    : ℕ → ℕ → ℕ → Expr
  | m    : Expr
  | pi   : Expr
  | pi'  : Expr
  | imp  : Expr
  | imp' : Expr
  | hole : Expr
  | ty   : ℕ → Expr
  | prp  : Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr, Lean.ToExpr

inductive ExprBox (e : Ast.Expr) where
  | mk : ExprBox e

declare_syntax_cat skmexpr
syntax "K" term:max term:max          : skmexpr
syntax "S" term:max term:max term:max : skmexpr
syntax "M"                            : skmexpr
syntax "~>"                           : skmexpr
syntax "<~"                           : skmexpr
syntax "→"                            : skmexpr
syntax "←"                            : skmexpr
syntax "Ty" term                      : skmexpr
syntax "Prp"                          : skmexpr
syntax "_"                            : skmexpr
syntax skmexpr "~>" skmexpr           : skmexpr
syntax skmexpr "<~" skmexpr           : skmexpr
syntax skmexpr "→" skmexpr            : skmexpr
syntax skmexpr "←" skmexpr            : skmexpr
syntax "(" skmexpr skmexpr ")"        : skmexpr
syntax ident                          : skmexpr
syntax "#" term                       : skmexpr
syntax "(" skmexpr ")"                : skmexpr

syntax "⟪" skmexpr "⟫"      : term
syntax "SKM[" skmexpr "]"   : term

macro_rules
  | `(SKM[ $e:skmexpr ])  => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K $m:term $n:term ⟫)            => `(Expr.k $m $n)
  | `(⟪ S $m:term $n:term $o:term ⟫)    => `(Expr.s $m $n $o)
  | `(⟪ M ⟫)                            => `(Expr.m)
  | `(⟪ _ ⟫)                            => `(Expr.hole)
  | `(⟪ Ty $n:term ⟫)                   => `(Expr.ty $n)
  | `(⟪ Prp ⟫)                          => `(Expr.prp)
  | `(⟪ ~> ⟫)                           => `(Expr.pi)
  | `(⟪ <~ ⟫)                           => `(Expr.pi')
  | `(⟪ → ⟫)                            => `(Expr.imp)
  | `(⟪ ← ⟫)                            => `(Expr.imp')
  | `(⟪ $e₁:skmexpr ~> $e₂:skmexpr ⟫)   => `(Expr.call (Expr.call Expr.pi ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e₁:skmexpr <~ $e₂:skmexpr ⟫)   => `(Expr.call (Expr.call Expr.pi' ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e₁:skmexpr → $e₂:skmexpr ⟫)    => `(Expr.call (Expr.call Expr.imp ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e₁:skmexpr ← $e₂:skmexpr ⟫)    => `(Expr.call (Expr.call Expr.imp' ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e:ident ⟫)                     => `($e)
  | `(⟪ # $e:term ⟫)                    => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                 => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)    => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

namespace Expr

def toStringImpl (e : Expr) : String :=
  match e with
  | SKM[S _m n o]  => s!"S.{_m},{n},{o}"
  | SKM[K _m n]    => s!"K.{_m},{n}"
  | SKM[M]    => "M"
  | SKM[Ty n] => s!"Type {n}"
  | SKM[Prp]  => "Prop"
  | SKM[_]    => "_"
  | SKM[~>]  => "~>"
  | SKM[<~]  => "<~"
  | SKM[→]  => "→"
  | SKM[←]  => "←"
  | SKM[(t_in ~> t_out)] => s!"({t_in.toStringImpl} ~> {t_out.toStringImpl})"
  | SKM[(t_in <~ t_out)] => s!"({t_in.toStringImpl} <~ {t_out.toStringImpl})"
  | SKM[(t_in → t_out)] => s!"({t_in.toStringImpl} → {t_out.toStringImpl})"
  | SKM[(t_in ← t_out)] => s!"({t_in.toStringImpl} ← {t_out.toStringImpl})"
  | SKM[(lhs rhs)] => s!"({lhs.toStringImpl} {rhs.toStringImpl})"

instance : ToString Expr where
  toString := toStringImpl

def fromExpr (e : Lean.Expr) : Option Expr :=
  match e with
  | .const `Expr.hole [] => pure SKM[_]
  | (.app
      (.app (.const `Expr.k []) (.lit (.natVal _m)))
      (.lit (.natVal n)))    => pure SKM[K _m n]
  | (.app
      (.app
        (.app (.const `Expr.s []) (.lit (.natVal _m)))
        (.lit (.natVal n))) (.lit (.natVal o)))    => pure SKM[S _m n o]
  | .const `Expr.m []    => pure SKM[M]
  | .const `Expr.pi [] => pure SKM[~>]
  | .const `Expr.pi' [] => pure SKM[<~]
  | .const `Expr.imp [] => pure SKM[→]
  | .const `Expr.imp' [] => pure SKM[←]
  | .sort .zero => pure SKM[Prp]
  | .sort n => pure SKM[Ty n.depth.pred]
  | .app (.app (.const `Expr.call []) lhs) rhs => do
    let lhs' ← fromExpr lhs
    let rhs' ← fromExpr rhs
    pure SKM[(lhs' rhs')]
  | _ => none

def mk_s_type (t_α α β γ : Ast.Expr) : Ast.Expr :=
  SKM[_]

def mk_k_type (_m n : ℕ) : Ast.Expr :=
  SKM[Ty _m ~> Ty n ~> (((((S _m.succ n.succ _m (M (~>))) (M (<~))) Ty _m) (~>)) (←))]

def max_universe : Expr → ℕ
  | SKM[K _m n] => max _m n
  | SKM[S _m n o] => max (max _m n) o
  | SKM[Ty n] => n
  | SKM[(lhs rhs)] => max lhs.max_universe rhs.max_universe
  | _ => 0

end Expr

end Ast
