import Mathlib.Tactic
import Lean
import Lean.Elab.Term

namespace Ast

abbrev Universe := ℕ

inductive Expr where
  | k    : Universe → Universe → Expr
  | s    : Universe → Universe → Universe → Expr
  | m    : Expr
  | pi   : Expr
  | pi'  : Expr
  | imp  : Expr
  | imp' : Expr
  | hole : Expr
  | ty   : Universe → Expr
  | prp  : Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr, Lean.ToExpr

def max_universe : Expr → Universe
  | .k _m n => max _m n
  | .s _m n o => max (max _m n) o
  | .ty n => n
  | .call lhs rhs => max (max_universe lhs) (max_universe rhs)
  | _ => 0

inductive ExprBox (e : Ast.Expr) where
  | mk : ExprBox e

declare_syntax_cat skmexpr
syntax "K" term:max term:max                           : skmexpr
syntax "K₀"                                            : skmexpr
syntax "S" term:max term:max term:max                  : skmexpr
syntax "I" skmexpr                                     : skmexpr
syntax "S₀"                                            : skmexpr
syntax "M"                                             : skmexpr
syntax "~>"                                            : skmexpr
syntax "<~"                                            : skmexpr
syntax "→" skmexpr skmexpr                             : skmexpr
syntax "←" skmexpr skmexpr                             : skmexpr
syntax "Ty" term                                       : skmexpr
syntax "Prp"                                           : skmexpr
syntax "?"                                             : skmexpr
syntax skmexpr "~>" skmexpr                            : skmexpr
syntax skmexpr "<~" skmexpr                            : skmexpr
syntax "(" skmexpr ":" skmexpr ")" "→" "(" skmexpr ":" skmexpr ")" : skmexpr
syntax skmexpr "←" skmexpr                             : skmexpr
syntax "(" skmexpr skmexpr ")"                         : skmexpr
syntax ident                                           : skmexpr
syntax "#" term                                        : skmexpr
syntax "(" skmexpr ")"                                 : skmexpr

syntax "⟪" skmexpr "⟫"      : term
syntax "SKM[" skmexpr "]"   : term

macro_rules
  | `(SKM[ $e:skmexpr ])  => `(⟪ $e ⟫)

/-
Can we define the type of K without ~>?

Also, idea. We can just specify type universes for →.

→ Ty m Ty n α β = K Ty m Ty n → K Ty m Ty n
Yes, we can derive →
-/

macro_rules
  | `(⟪ K $m:term $n:term ⟫)            => `(Expr.k $m $n)
  | `(⟪ S $m:term $n:term $o:term ⟫)    => `(Expr.s $m $n $o)
  | `(⟪ K₀ ⟫)                           => `(Expr.k 0 0)
  | `(⟪ S₀ ⟫)                           => `(Expr.s 0 0 0)
  | `(⟪ M ⟫)                            => `(Expr.m)
  | `(⟪ ? ⟫)                            => `(Expr.hole)
  | `(⟪ Ty $n:term ⟫)                   => `(Expr.ty $n)
  | `(⟪ Prp ⟫)                          => `(Expr.prp)
  | `(⟪ ~> ⟫)                           => `(Expr.pi)
  | `(⟪ <~ ⟫)                           => `(Expr.pi')
  | `(⟪ → $t₁ $t₂ ⟫)                    => `(Expr.imp)
  | `(⟪ ← $t₁ $t₂ ⟫)                    => `(Expr.imp')
  | `(⟪ $e₁:skmexpr ~> $e₂:skmexpr ⟫)   => `(Expr.call (Expr.call Expr.pi ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e₁:skmexpr <~ $e₂:skmexpr ⟫)   => `(Expr.call (Expr.call Expr.pi' ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ ($e₁:skmexpr : $t₁:skmexpr) → ($e₂:skmexpr : $t₂:skmexpr) ⟫) => `(SKM[((((→ $t₁) $t₂) $e₁) $e₂)])
  | `(⟪ $e₁:skmexpr ← $e₂:skmexpr ⟫)    => `(SKM[((← $e₁) $e₂)])
  | `(⟪ $e:ident ⟫)                     => `($e)
  | `(⟪ # $e:term ⟫)                    => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                 => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)    => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

namespace Expr

def insert_arrow_arg (in_e e : Ast.Expr) : Ast.Expr :=
  match in_e with
  | SKM[(t_in ~> t_out)] =>
    SKM[(#(insert_arrow_arg t_in e) ~> #(insert_arrow_arg t_out e))]
  | x => SKM[(x e)]

def pop_arrow : Ast.Expr → Ast.Expr
  | SKM[(_t_in ~> t_out)]
  | SKM[(_t_in → t_out)]
  | SKM[(t_out <~ _t_in)]
  | SKM[(t_out ← _t_in)] => t_out
  | e => e

end Expr

def mk_k_type_eta (α β : Expr) : Expr :=
  let α_u := max_universe α
  let β_u := max_universe α

  let inner_k := SKM[((((K α_u β_u) (M α)) (M β)) α)]

  SKM[(α ~> (β ~> ((((K (max α_u β_u).succ α_u) (M inner_k)) α) inner_k)))]

def i (t : Expr) : Expr :=
  let u := max_universe t
  let t_k_right := mk_k_type_eta t t

  let k_right := SKM[(((K u u) t) t)]
  let k_left := SKM[(((K u (max_universe k_right)) t) #(t_k_right))]

  SKM[((((((S u u.succ u.succ) t) (t ~> t)) t) k_left) k_right)]

syntax "I" skmexpr : skmexpr

macro_rules
  | `(⟪ I $t:skmexpr ⟫) => `(SKM[#(i ⟪$t⟫)])

def mk_k_type (_m n : Universe) : Ast.Expr :=
  SKM[Ty _m ~> Ty n ~> (((((K _m n) Ty _m) Ty n) (~>)) (<~))]

namespace Expr

def toStringImpl (e : Expr) : String :=
  match e with
  | SKM[S 0 0 0]   => "S₀"
  | SKM[K 0 0]   => "K₀"
  | SKM[S _m n o]  => s!"S.{_m},{n},{o}"
  | SKM[K _m n]    => s!"K.{_m},{n}"
  | SKM[M]    => "M"
  | SKM[Ty n] => s!"Type {n}"
  | SKM[Prp]  => "Prop"
  | SKM[?]    => "?"
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
  | .const `Expr.hole [] => pure SKM[?]
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

/-
K type with dependent arrow:

K α : (K α) ~> (~> α)
K : S (K ~>) (S K ~>)
-/

end Expr

end Ast
