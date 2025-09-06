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
syntax "@K" term:max term:max                          : skmexpr
syntax "K" skmexpr skmexpr                             : skmexpr
syntax "S" skmexpr skmexpr skmexpr                     : skmexpr
syntax "K₀"                                            : skmexpr
syntax "@S" term:max term:max term:max                 : skmexpr
syntax "I" skmexpr                                     : skmexpr
syntax "S₀"                                            : skmexpr
syntax "M"                                             : skmexpr
syntax "~>"                                            : skmexpr
syntax "<~"                                            : skmexpr
syntax "→" skmexpr skmexpr                             : skmexpr
syntax "←" skmexpr skmexpr                             : skmexpr
syntax "always" skmexpr                                : skmexpr
syntax "Ty" term                                       : skmexpr
syntax "Prp"                                           : skmexpr
syntax "?"                                             : skmexpr
syntax skmexpr "~>" skmexpr                            : skmexpr
syntax skmexpr "<~" skmexpr                            : skmexpr
syntax skmexpr "→" skmexpr                             : skmexpr
syntax skmexpr "←" skmexpr                             : skmexpr
syntax "(" skmexpr skmexpr ")"                         : skmexpr
syntax ident                                           : skmexpr
syntax "#" term                                        : skmexpr
syntax "(" skmexpr ")"                                 : skmexpr

syntax "⟪" skmexpr "⟫"      : term
syntax "SKM[" skmexpr "]"   : term

macro_rules
  | `(SKM[ $e:skmexpr ])  => `(⟪ $e ⟫)

macro_rules
  | `(⟪ α ~> always $t:skmexpr ⟫)        => `(SKM[α ~> (K ? α $t)])
  | `(⟪ @K $m:term $n:term ⟫)            => `(Expr.k $m $n)
  | `(⟪ @S $m:term $n:term $o:term ⟫)    => `(Expr.s $m $n $o)
  | `(⟪ K $m:skmexpr $n:skmexpr ⟫)       => `(SKM[(((@K (max_universe ⟪$m⟫) (max_universe ⟪$n⟫)) $m) $n)])
  | `(⟪ (K ? $t_y:skmexpr $e) ⟫)         => `(SKM[((K (M $e) $t_y) $e)])
  | `(⟪ S $m:skmexpr $n:skmexpr $o:skmexpr ⟫) => `(SKM[((((@S (max_universe ⟪$m⟫) (max_universe ⟪$n⟫) (max_universe ⟪$o⟫)) $m) $n) $o)])
  | `(⟪ K₀ ⟫)                           => `(Expr.k 0 0)
  | `(⟪ S₀ ⟫)                           => `(Expr.s 0 0 0)
  | `(⟪ M ⟫)                            => `(Expr.m)
  | `(⟪ ? ⟫)                            => `(Expr.hole)
  | `(⟪ Ty $n:term ⟫)                   => `(Expr.ty $n)
  | `(⟪ Prp ⟫)                          => `(Expr.prp)
  | `(⟪ ~> ⟫)                           => `(Expr.pi)
  | `(⟪ <~ ⟫)                           => `(Expr.pi')
  | `(⟪ $e₁:skmexpr ~> $e₂:skmexpr ⟫)   => `(Expr.call (Expr.call Expr.pi ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e₁:skmexpr <~ $e₂:skmexpr ⟫)   => `(Expr.call (Expr.call Expr.pi' ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e₁:skmexpr → $e₂:skmexpr ⟫)    => `(SKM[(((→ (M$e₁) (M$e₂)) $e₁) $e₂)])
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
  | SKM[(t_out <~ _t_in)] => t_out
  | e => e

end Expr

def mk_k_type_eta (α β : Expr) : Expr :=
  let inner_k := SKM[((K ? (M β)) α)]

  SKM[(α ~> (β ~> ((K ? α) inner_k)))]

syntax "I" skmexpr : skmexpr

/-
Can we define the type of K without ~>?

Also, idea. We can just specify type universes for →.

→ Ty m Ty n α β = K Ty m Ty n ~> K Ty m Ty n
Yes, we can derive →
→ = K ~> K

Need to flip the left side.
S K I

Wait, this is eta expanded.
This is slightly more complicated than I thought, but it's fine.

→ Ty m Ty n α β = Ty m

-- This gives us α on the left at the end
-- We want β on the right hand side
-- This use of id is wrong
S (K K) I Ty m = K (I Ty m)
K (I Ty m) α = (I Ty m)
(I Ty m ) β = β

Yeah. what? This is all wrong.
We need to also reject the argument.

Wait oh shit!!!

→ = ~>

→ α β = α ~> β

So we can probably do some shit like:

→ α β = K α ~> K β

This is kind of hairy to fill the type arguments of. Ngl.

→ α β = K Ty m α α ~> K Ty n α β

We can already fill in Ty m and Ty n with eta expansion.

→ Ty m Ty n = K Ty m ~> K Ty n
Now when we apply α we get
→ Ty m Ty n α = K Ty m α ~> K Ty n α
This is exactly right

Just for the β case, we need some magic
→ Ty m Ty n α β = K Ty m α β ~> K Ty n α β

We need to switch β here.

→ Ty m Ty n α β = K (K Ty m α α) β ~> K Ty n α β

left hand side:

S (K Ty m) (I Ty m) α = K Ty m α α
S (M (K Ty m)) (M (I Ty m))

Sot this is for the right side actually.

rhs α β x = α

We can only use always in macro form unfortunately.

→ Ty m Ty n α β = K α ~> K β

This is really simple except for the damn type arguments

We could make a little "dumb" inference method.
Fill types or something.

Fill types would be very useful in general.
Fills in placeholders.

→ Ty m Ty n α β = K Ty m α α ~> K Ty n α β

So we just need to copy α into the K's

(K Ty m ~> K Ty n) α = K Ty m α ~> K Ty n α

This is fine for the right hand side.

Rhs = K Ty n
Lhs needs to copy α.

lhs = S (K Ty m) (I Ty m)
lhs α = K Ty m α α



-/

macro_rules
  | `(⟪ → $t₁ $t₂ ⟫)    => `(Expr.imp)
  | `(⟪ ← $t₁ $t₂ ⟫)    => `(Expr.imp')

def i (t : Expr) : Expr :=
  let t_k_right := mk_k_type_eta t t

  let k_right := SKM[(K t t)]
  let k_left := SKM[(K t t_k_right)]

  SKM[(((S t (t → t) t) k_left) k_right)]

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
