/-
# Examples of Dependent Types using Definitions

## Combinator Definitions

-/

import Mathlib.Tactic

abbrev K₀.{m, n} := ∀ (α : Type m) (β : Type n) (_x : α) (_y : β), α
def K₁ : K₀ := fun _α _β x _y => x

abbrev S₀.{m, n, o} := ∀ (α : Type m) (β : Type n) (γ : Type o) (_x : α → β → γ) (_y : α → β) (_z : α), γ
def S₁ : S₀ := fun _α _β _γ x y z => x z (y z)

/-
## \\(M\\) combinator

Normal \\(\Pi\\) typing:

\\(\Pi (x : A), B x\\)

`M` is basically the `I` combinator, but it allows reflection at runtime.
We can derive a few useful higher-typing combinator using this base combinator:

$$
M\ (e : t) = t \\\\
M_{\circ}\ (e : t) = e\ t = e\ (M\ e) = S\ (SKS)\ M\ e \\\\
M_{s}\ (e : t)\ arg = e\ arg\ (t\ arg) = S\ e\ t\ arg = S\ e\ (M\ e)\ arg = S\ S\ M\ e\ arg
$$

Notably, this allows us to fully eliminate binders in all types.

$$
K : K \\\\
(K \mathbb{N} : K (M \mathbb{N}))
$

However, we quickly run into issues. We shouldn't be able to produce an expression of type `False`.

$$
false := SK \\\\
? : false \\\\
false : (M S) (M K) \rightarrow false : S K \rightarrow false : false \\\\
\textbf{contradiction.}
$$

However, if we introduce type universes, we easily get around this paradox:

$$
K_{0} : K_{1} \\\\
M K_{0} = K{1}
$$
-/

begin mutual

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
syntax "K" ident               : skmexpr
syntax "S" ident               : skmexpr
syntax "M" ident               : skmexpr
syntax "K" num                 : skmexpr
syntax "S" num                 : skmexpr
syntax "M" num                 : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax ident                   : skmexpr
syntax "(" skmexpr ")"         : skmexpr

syntax " ⟪ " skmexpr " ⟫ "     : term

macro_rules
  | `(⟪ K $u:ident ⟫)                     => `(Expr.k (.mk $u))
  | `(⟪ S $u:ident ⟫)                     => `(Expr.s (.mk $u))
  | `(⟪ M $u:ident ⟫)                     => `(Expr.m (.mk $u))
  | `(⟪ K $u:num ⟫)                     => `(Expr.k (.mk $u))
  | `(⟪ S $u:num ⟫)                     => `(Expr.s (.mk $u))
  | `(⟪ M $u:num ⟫)                     => `(Expr.m (.mk $u))
  | `(⟪ $e:ident ⟫)                       => `($e)
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
      max (max_universe lhs) (max_universe rhs)

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

mutual

inductive is_eval_once : Expr → Expr → Prop
  | k x y n      : is_eval_once SKM[((K n x) y)] x
  | s x y z n    : is_eval_once SKM[(((S n x) y) z)] SKM[((x z) (y z))]
  | m e t n      : valid_judgment e t
    → is_eval_once SKM[((M n) e)] t
  | left         : is_eval_once lhs lhs'
    → is_eval_once SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right        : is_eval_once rhs rhs'
    → is_eval_once SKM[(lhs rhs)] SKM[(lhs rhs')]
  | k_rfl        : is_eval_once SKM[K n] SKM[K n]
  | s_rfl        : is_eval_once SKM[S n] SKM[S n]
  | m_rfl        : is_eval_once SKM[M n] SKM[M n]

inductive beta_eq : SkExpr → SkExpr → Prop
  | rfl                       : beta_eq e e
  | eval                      : is_eval_once e₁ e₂ → beta_eq e₁ e₂
  | left                      : beta_eq lhs lhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right                     : beta_eq rhs rhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')]
  | symm                      : beta_eq e₂ e₁ → beta_eq e₁ e₂
  | trans                     : beta_eq e₁ e₂ → beta_eq e₂ e₃ → beta_eq e₁ e₃

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
  | beta_eq e t₁ t₂           : valid_judgment e t₁ → beta_eq t₁ t₂ → valid_judgment e t₂

inductive valid_judgment_weak : Expr → Expr → Prop
  | k n                       : valid_judgment_weak SKM[K n] (.k (.mk n.succ))
  | s n                       : valid_judgment_weak SKM[S n] (.s (.mk n.succ))
  | m n                       : valid_judgment_weak SKM[M n] (.m (.mk n.succ))
  | call lhs rhs              : lhs.max_universe > rhs.max_universe
    → valid_judgment_weak lhs (.call (.mk (Expr.m (.mk lhs.max_universe.succ)) lhs))
    → valid_judgment_weak rhs (.call (.mk (Expr.m (.mk rhs.max_universe.succ)) rhs))
    → valid_judgment_weak SKM[(lhs rhs)]
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

end

mutual

partial def type_of (e : Expr) : Option Expr :=
  match e with
    | SKM[(K n)] => pure $ (.k (.mk n.succ))
    | SKM[(S n)] => pure $ (.s (.mk n.succ))
    | SKM[(M n)] => pure $ (.m (.mk n.succ))
    | SKM[(lhs rhs)] => do
      if rhs.max_universe ≥ lhs.max_universe then
        none
      else
        eval_unsafe (.call (.mk (← eval_unsafe (.call (.mk (.m (.mk lhs.max_universe.succ)) lhs))) (← eval_unsafe (.call (.mk (.m (.mk rhs.max_universe.succ)) rhs)))))

partial def eval_unsafe (e : Expr) : Option Expr :=
  match e with
    | SKM[(((K _n) x) _y)]    => eval_unsafe x
    | SKM[((((S _n) x) y) z)] => eval_unsafe SKM[((x z) (y z))]
    | SKM[(M _n e)] => do eval_unsafe (← type_of e)
    | SKM[(lhs rhs)] => do
      let lhs' ← eval_unsafe lhs

      if SKM[(lhs' rhs)] = SKM[(lhs rhs)] then
        some SKM[(lhs rhs)]
      else
        eval_unsafe SKM[(lhs' rhs)]
    | x => x

partial def eval_once (e : Expr) : Option Expr :=
  match e with
    | SKM[(((K _n) x) _y)] => x
    | SKM[((((S _n) x) y) z)] => SKM[((x z) (y z))]
    | SKM[(M _n e)] => type_of e
    | SKM[(lhs rhs)] => do
      let lhs' ← eval_once lhs

      SKM[(lhs' rhs)]
    | x => x

end

/-
## Strong Normalization

A strong proof of consistency involves proving that every well-typed expression terminates. I do so. I utilize the typical reducibility candidates strategy.
-/

inductive sn : Expr → Prop
  | trivial  : is_eval_once e e  → sn e
  | hard     : is_eval_once e e' → sn e' → sn e

/-
Note that we define evaluation as a relation on expressions. This is due to `eval_once`'s dependence on the type of `e`. This appears problematic and confusing. However, we can still prove membership in R of all well-typed expressions.
-/

lemma k_eval_sn : ∀ n x y, sn x → sn SKM[((K n x) y)] := by
  intro n x y sn_x
  apply sn.hard
  apply is_eval_once.k
  exact sn_x

lemma s_eval_sn : ∀ n x y z, sn SKM[((x z) (y z))] → sn SKM[(((S n x) y) z)] := by
  intro n x y z sn_eval
  apply sn.hard
  apply is_eval_once.s
  exact sn_eval

/-
## Type Preservation

To prove preservation, we prove that we can derive typings for `(K (x : α) y : α)` from our base typing rules using `M`.

Note that our typing rules make extensive use of the `M` combinator for "reflection." We can use an `S`-transformation rule like such:

$$
(e_{1}\ e_{2} : M\ e_{1}\ e_{2}) \implies (e_{1}\ e_{2} : (M\ e_{1})\ (M\ e_{2}))
$$

This shortens our type preservation proof significantly by allowing us to collapse expressions of the form \\((M K arg)\\) to reducible \\((M K) (M arg)\\) expressions.
-/

lemma congr_m : is_eval_once a b → beta_eq SKM[((M 0) a)] SKM[((M 0) b)] := by
  intro h
  apply beta_eq.trans
  apply beta_eq.right
  exact beta_eq.eval h
  exact beta_eq.rfl

lemma valid_judgment_imp_m : ∀ n, valid_judgment e t → valid_judgment e SKM[((M n) e)] := by
  intro n h
  apply valid_judgment.beta_eq
  exact h
  apply beta_eq.symm
  apply beta_eq.eval
  apply is_eval_once.m
  exact h

lemma eval_preserves_judgment : ∀ e e' t, valid_judgment e t → is_eval_once e e' → valid_judgment e' t' → valid_judgment e' t := by
  intro c e' t h_t h_eval h_t'
  cases h_eval
  case k y n =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m (e'.max_universe.succ)
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
    apply beta_eq.symm
    apply beta_eq.trans
    apply beta_eq.symm
    apply beta_eq.eval
    apply is_eval_once.m
    use 0
    exact h_t
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.right
    apply is_eval_once.k
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
  case s x y z n =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m (SKM[((x z) (y z))].max_universe.succ)
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
    apply beta_eq.symm
    apply beta_eq.trans
    apply beta_eq.symm
    apply beta_eq.eval
    apply is_eval_once.m
    use 0
    exact h_t
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.right
    apply is_eval_once.s
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
  case m e'' n h =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m (e''.max_universe.succ)
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
    apply beta_eq.symm
    apply beta_eq.trans
    apply beta_eq.symm
    apply beta_eq.eval
    apply is_eval_once.m
    use 0
    exact h_t
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.right
    apply is_eval_once.m
    exact h
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t'
  case left lhs lhs' rhs h_eq =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m
    use 0
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.right
    apply beta_eq.left
    apply beta_eq.symm
    apply beta_eq.eval h_eq
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t
  case right rhs rhs' lhs h_eq =>
    apply valid_judgment.beta_eq
    apply valid_judgment_imp_m
    use 0
    exact h_t'
    apply beta_eq.trans
    apply beta_eq.right
    apply beta_eq.right
    apply beta_eq.symm
    apply beta_eq.eval h_eq
    apply beta_eq.eval
    apply is_eval_once.m
    exact h_t
  case k_rfl =>
    exact h_t
  case s_rfl =>
    exact h_t
  case m_rfl =>
    exact h_t

lemma valid_judgment_call_imp_n_bounds : valid_judgment_weak SKM[(lhs rhs)] t → lhs.max_universe > rhs.max_universe := by
  intro h
  cases h
  case call _ _ h_u =>
    exact h_u

lemma weakening : valid_judgment_weak e t → valid_judgment e t := by
  intro h
  cases h
  case k =>
    apply valid_judgment.k
  case s =>
    apply valid_judgment.s
  case m =>
    apply valid_judgment.m
  case call lhs rhs h_u h_t_lhs h_t_rhs =>
    apply valid_judgment.call
    exact h_u
    apply weakening at h_t_lhs
    exact h_t_lhs
    apply weakening at h_t_rhs
    exact h_t_rhs

lemma eval_preserves_judgment_hard : ∀ e e' t, valid_judgment_weak e t → is_eval_once e e' → valid_judgment_weak e' t := by
  intro e e' t h_t h_eval
  cases h_t
  case k n =>
    cases h_eval
    case k_rfl =>
      apply valid_judgment_weak.k
  case s =>
    cases h_eval
    case s_rfl =>
      apply valid_judgment_weak.s
  case m =>
    cases h_eval
    case m_rfl =>
      apply valid_judgment_weak.m
  case call lhs rhs h_u h_t_lhs h_t_rhs  =>
    match h₀ : h_eval with
      | .k lhs' rhs' n =>
        cases h_t_lhs
      | .s x' y' z' n =>
        cases h_t_lhs
      | .left h_eval' =>
        cases h_t_lhs
      | .right h_eval' =>
        cases h_t_lhs
      | .m e t n h_t =>
        cases h_t_lhs

lemma all_sn_eval_once : ∀ e, sn e → ∃ e', is_eval_once e e' := by
  intro e h
  cases h
  case trivial h =>
    use e
  case hard e' h_sn h_step =>
    use e'

lemma is_eval_once_rfl : is_eval_once e e → e = e := by
  intro h
  cases h
  case m =>
    rfl
  case left =>
    rfl
  case right =>
    rfl
  case k_rfl =>
    rfl
  case s_rfl =>
    rfl
  case m_rfl =>
    rfl

theorem all_well_typed_sn (e : Expr) (t : Expr) : valid_judgment e t → sn e := by
  intro h_t
  match e with
    | SKM[((K n x) y)] =>
      apply sn.hard
      apply is_eval_once.k
      
      sorry
    | SKM[(((S n x) y) z)] =>
      sorry
    | SKM[(M n e)] => sorry
    | SKM[(lhs rhs)] => sorry
    | .k (.mk n) =>
      apply sn.trivial
      exact is_eval_once.k_rfl
    | .s (.mk n) =>
      apply sn.trivial
      exact is_eval_once.s_rfl
    | .m (.mk n) =>
      apply sn.trivial
      exact is_eval_once.m_rfl
termination_by e

/-
#### Ramblings

M_id (e : t) = t := M 

We want:

(K (Nat : Typea) Real : Typea)
(K Nat Real : K Typea Typeb)
(K Nat Real : M K )
(K Nat Real : M 

we can quickly see that we have a more specific version of M that becomes useful:

M_1 (e : t) arg = arg t

We can actually derive this from the existing combinators. I will do this later.

(K Nat Real : K (M_1 Nat) (M_1 Real))

I define SR = S (S (K K) (S K S)) (K (S K S K))

SR M_1 Nat Real = (M_1 Nat) (M_1 Real)

K (SR M_1 Nat Real) = (M_1 Nat) (M_1 Real)

So, we define the typing judgment:

(x : t) (y : t) : x (M_1 x) 

Eh this doesn't generalize well.
Also, let's take an example. Identify function.

((S : S) (K : K) (S : S)) : S 
-/
