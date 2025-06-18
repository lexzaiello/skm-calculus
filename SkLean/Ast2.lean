import Mathlib.Tactic

mutual

inductive M where
  | mk :  ℕ → M
deriving Repr

inductive S where
  | mk : ℕ → S
deriving DecidableEq, Repr, BEq

inductive K where
  | mk : ℕ → K
deriving DecidableEq, Repr, BEq

inductive Call where
  | mk : Expr → Expr → Call
deriving DecidableEq, Repr, BEq

inductive Expr where
  | m    : M → Expr
  | k    : K → Expr
  | s    : S → Expr
  | call : Call → Expr
deriving DecidableEq, Repr, BEq

end

namespace Call

def lhs : Call → Expr
  | .mk lhs _ => lhs

def rhs : Call → Expr
  | .mk _ rhs => rhs

end Call

/-
## DSL

We make use of a small DSL for legibility.
-/

declare_syntax_cat skmexpr
syntax "K" term                : skmexpr
syntax "S" term                : skmexpr
syntax "M" term                : skmexpr
syntax "K" num                 : skmexpr
syntax "S" num                 : skmexpr
syntax "M" num                 : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax ident                   : skmexpr
syntax "#" term                : skmexpr
syntax "(" skmexpr ")"         : skmexpr

syntax " ⟪ " skmexpr " ⟫ "     : term

macro_rules
  | `(⟪ K $u:term ⟫)                      => `(Expr.k (.mk $u))
  | `(⟪ S $u:term ⟫)                      => `(Expr.s (.mk $u))
  | `(⟪ M $u:term ⟫)                      => `(Expr.m (.mk $u))
  | `(⟪ K $u:num ⟫)                       => `(Expr.k (.mk $u))
  | `(⟪ S $u:num ⟫)                       => `(Expr.s (.mk $u))
  | `(⟪ M $u:num ⟫)                       => `(Expr.m (.mk $u))
  | `(⟪ $e:ident ⟫)                       => `($e)
  | `(⟪ # $e:term ⟫)                      => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                   => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)      => `(Expr.call (.mk ⟪ $e₁ ⟫ ⟪ $e₂ ⟫))

syntax "SKM[ " skmexpr " ] "        : term
syntax "SKC[" skmexpr skmexpr "]" : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

macro_rules
  | `(SKC[ $e₁:skmexpr $e₂:skmexpr ]) => `(Call.mk ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

namespace Expr

def max_universe (e : Expr) : ℕ :=
  match e with
    | SKM[(K n)] => n
    | SKM[(S n)] => n
    | SKM[(M n)] => n
    | SKM[(lhs rhs)] =>
      (max_universe lhs) + (max_universe rhs)

def min_universe (e : Expr) : ℕ :=
  match e with
    | SKM[(K n)] => n
    | SKM[(S n)] => n
    | SKM[(M n)] => n
    | SKM[(lhs rhs)] =>
      min (max_universe lhs) (max_universe rhs)

inductive valid_universes : Expr → Prop
  | k    : valid_universes SKM[(K n)]
  | s    : valid_universes SKM[(S n)]
  | m    : valid_universes SKM[(M n)]
  | call : lhs.max_universe > rhs.max_universe
    → valid_universes lhs
    → valid_universes rhs
    → valid_universes SKM[(lhs rhs)]

end Expr

/-
## Judgment Rules

`K`, `M`, and `S` must be well-typed on their own. We need some expression that can represent the type of `K`. One option is the \\(\rightarrow\\) type constructor from the SLTC or System F. The typing of \\(S\\) and \\(K\\) are fairly obvious. However, the typing of \\(M\\) is not. It's not immediately clear that we need typing judgment rules for `K`, `M`, or `S` alone. There is no way to explicitly assign a type to `K`, `M`, or `S`. They just are. However, there are emergent rules for application. The typical rules for application in the SK combinator calculus are as follows:

$$
K : \alpha \rightarrow \beta \rightarrow \alpha \\\\
S : (\alpha \rightarrow \beta \rightarrow \gamma) \rightarrow (\alpha \rightarrow \beta) \rightarrow \alpha \rightarrow \gamma \\\\
M : hmm
$$

Typing rules quickly beome complicated. We would prefer to avoid binders in our type discipline. We can create an "emergent" typing based on function application.

$$
\frac{
  \Gamma \vdash e_{1} : T
}{
  \Gamma \vdash K\ e_{1}\ e_{2} : T
}
$$
$$
\frac{
  \Gamma \vdash f_{1}\ \text{arg}\ (f_{2}\ \text{arg}) : T)
}{
  \Gamma \vdash S\ f_{1}\ f_{2}\ \text{arg} : T
}
$$

But what is the type of \\(K\\)? It's not really obvious. Clearly, we need some way to represent the type of \\(K\\) that avoids binders. Recall that:

$$
Kxy = x
$$

The type of \\(K\\) is typically \\(\alpha \rightarrow \beta \rightarrow \alpha\\). Its type is of the form of the \\(K\\) combinator. We can thus define a typing as such:

$$
K : K
$$

This typing is coherent under an evaluation rule for the \\(M\\) combinator:

$$
M\ (x : t)\ \text{arg} = \text{arg}\ x\ (\text{arg}\ t) \\\\
M\ \mathbb{N}\ K = K\ \mathbb{N}\ (K\ \text{Type}) = \mathbb{N} \\\\
M\ K\ K = K\ K\ (K\ K) = K
$$
-/

inductive valid_judgment : Expr → Expr → Prop
  | k n                       : valid_judgment SKM[K n] (.k (.mk n.succ))
  | s n                       : valid_judgment SKM[S n] (.s (.mk n.succ))
  | m n                       : valid_judgment SKM[M n] (.m (.mk n.succ))
  | call lhs rhs              : lhs.max_universe > rhs.max_universe
    → valid_judgment lhs (.call (.mk (Expr.m (.mk lhs.max_universe.succ)) lhs))
    → valid_judgment rhs (.call (.mk (Expr.m (.mk rhs.max_universe.succ)) rhs))
    → valid_judgment SKM[(lhs rhs)]
      (.call (.mk
        (.call (.mk
          (Expr.m (.mk lhs.max_universe.succ))
          lhs
        ))
        (.call (.mk
          (Expr.m (.mk rhs.max_universe.succ))
          rhs
        ))
      ))

inductive is_eval_once : Expr → Expr → Prop
  | k x y n            : is_eval_once SKM[(((K n) x) y)] x
  | s x y z n          : is_eval_once SKM[((((S n) x) y) z)] SKM[((x z) (y z))]
  | m_final e t        : valid_judgment e t
    → is_eval_once SKM[((M e.max_universe.succ) e)] t
  | m_step             : is_eval_once e e'
    → is_eval_once SKM[((M e.max_universe.succ) e)] SKM[((M e'.max_universe.succ) e')]
  | left         : is_eval_once lhs lhs'
    → is_eval_once SKM[(lhs rhs)] SKM[(lhs' rhs)]

inductive beta_eq : SkExpr → SkExpr → Prop
  | rfl                       : beta_eq e e
  | eval                      : is_eval_once e₁ e₂ → beta_eq e₁ e₂
  | left                      : beta_eq lhs lhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right                     : beta_eq rhs rhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')]
  | trans                     : beta_eq e₁ e₂      → beta_eq e₂ e₃ → beta_eq e₁ e₃
  | symm                      : beta_eq e₁ e₂      → beta_eq e₂ e₁


inductive is_normal_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e'))                 → is_normal_n 0 e e
  | one   : is_eval_once e e                             → is_normal_n 1 e e
  | succ  : is_eval_once e e' → is_normal_n n e' e_final → is_normal_n n.succ e e_final

namespace is_normal_n

lemma m_stuck : is_normal_n 0 SKM[M n] SKM[M n] := by
  apply is_normal_n.stuck
  intro h
  obtain ⟨e', h_eval⟩ := h
  cases h_eval

lemma k_stuck : is_normal_n 0 SKM[K n] SKM[K n] := by
  apply is_normal_n.stuck
  intro h
  obtain ⟨e', h_eval⟩ := h
  cases h_eval

lemma s_stuck : is_normal_n 0 SKM[S n] SKM[S n] := by
  apply is_normal_n.stuck
  intro h
  obtain ⟨e', h_eval⟩ := h
  cases h_eval

end is_normal_n

