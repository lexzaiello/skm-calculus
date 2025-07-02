import Mathlib.Tactic

inductive Expr where
  | m    : ℕ → Expr
  | k    : ℕ → Expr
  | s    : ℕ → Expr
  | call : Expr → Expr → Expr
deriving DecidableEq, Repr, BEq

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
  | `(⟪ K $u:term ⟫)                      => `(Expr.k $u)
  | `(⟪ S $u:term ⟫)                      => `(Expr.s $u)
  | `(⟪ M $u:term ⟫)                      => `(Expr.m $u)
  | `(⟪ K $u:num ⟫)                       => `(Expr.k $u)
  | `(⟪ S $u:num ⟫)                       => `(Expr.s $u)
  | `(⟪ M $u:num ⟫)                       => `(Expr.m $u)
  | `(⟪ $e:ident ⟫)                       => `($e)
  | `(⟪ # $e:term ⟫)                      => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                   => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)      => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

syntax "SKM[ " skmexpr " ] "      : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

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

namespace Expr

def sum_universes (e : Expr) : ℕ :=
  match e with
    | SKM[(K n)] => n
    | SKM[(S n)] => n
    | SKM[(M n)] => n
    | SKM[(lhs rhs)] => sum_universes lhs + sum_universes rhs

end Expr

@[simp]
abbrev trivial_typing (e : Expr) : Expr := SKM[((M e.sum_universes.succ) e)]

inductive is_eval_once : Expr → Expr → Prop
  | k x y n      : is_eval_once SKM[(((K n) x) y)] x
  | s x y z n    : is_eval_once SKM[((((S n) x) y) z)] SKM[((x z) (y z))]
  | m_k          : is_eval_once SKM[((M n.succ) (K n))] SKM[(K n.succ)]
  | m_s          : is_eval_once SKM[((M n.succ) (S n))] SKM[(S n.succ)]
  | m_m          : is_eval_once SKM[((M n.succ) (M n))] SKM[(M n.succ)]
  | m_call       : is_eval_once SKM[((M SKM[(lhs rhs)].sum_universes.succ) (lhs rhs))]
    SKM[(((M lhs.sum_universes.succ) lhs) ((M rhs.sum_universes.succ) rhs))]
  | left         : is_eval_once lhs lhs' → is_eval_once SKM[(lhs rhs)] SKM[(lhs' rhs)]

inductive beta_eq : SkExpr → SkExpr → Prop
  | rfl                       : beta_eq e e
  | eval                      : is_eval_once e₁ e₂ → beta_eq e₁ e₂
  | left                      : beta_eq lhs lhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right                     : beta_eq rhs rhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')]
  | trans                     : beta_eq e₁ e₂      → beta_eq e₂ e₃ → beta_eq e₁ e₃
  | symm                      : beta_eq e₁ e₂      → beta_eq e₂ e₁

inductive valid_judgment : Expr → Expr → Prop
  | k n                       : valid_judgment SKM[K n] (trivial_typing SKM[(K n)])
  | s n                       : valid_judgment SKM[S n] (trivial_typing SKM[(S n)])
  | m n                       : valid_judgment SKM[M n] (trivial_typing SKM[(M n)])
  | call_k₁                   : valid_judgment x t_x
    → valid_judgment SKM[((K n) x)] (trivial_typing SKM[((K n) x)])
  | call_s₁                   : valid_judgment x t_x
    → valid_judgment SKM[((S n) x)] (trivial_typing SKM[((S n) x)])
  | call_s₂                   : valid_judgment x t_x
    → valid_judgment y t_y
    → valid_judgment SKM[(((S n) x) y)] (trivial_typing SKM[(((S n) x) y)])
  | call_k                    : valid_judgment x t_x
    → valid_judgment y t_y
    → valid_judgment SKM[(((K n) x) y)] (trivial_typing SKM[(((K n) x) y)])
  | call_s                    : valid_judgment SKM[((x z) (y z))] t_call
    → valid_judgment x t_x
    → valid_judgment y t_y
    → valid_judgment z t_z
    → SKM[((x z) (y z))].sum_universes < SKM[(((((S n) x) y) z))].sum_universes
    → valid_judgment SKM[((((S n) x) y) z)] (trivial_typing SKM[((((S n) x) y) z)])
  | call_m                    : valid_judgment e t
    → valid_judgment SKM[((M n) e)] (trivial_typing SKM[((M n) e)])
  | call                      : valid_judgment lhs t_lhs
    → valid_judgment rhs t_rhs
    → is_eval_once SKM[(lhs rhs)] e'
    → SKM[(lhs rhs)].sum_universes < e'.sum_universes
    → valid_judgment SKM[(lhs rhs)] (trivial_typing SKM[(lhs rhs)])

inductive is_normal_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e'))                 → is_normal_n 0 e e
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
