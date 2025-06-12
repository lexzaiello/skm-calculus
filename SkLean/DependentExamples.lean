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
  | m e t        : valid_judgment e t
    → is_eval_once SKM[((M 0) e)] t
  | left         : is_eval_once lhs lhs'
    → is_eval_once SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right        : is_eval_once rhs rhs'
    → is_eval_once SKM[(lhs rhs)] SKM[(lhs rhs')]

inductive beta_eq : SkExpr → SkExpr → Prop
  | rfl                       : beta_eq e e
  | eval                      : is_eval_once e₁ e₂ → beta_eq e₁ e₂
  | left                      : beta_eq lhs lhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right                     : beta_eq rhs rhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')]
  | symm                      : beta_eq e₂ e₁ → beta_eq e₁ e₂
  | trans                     : beta_eq e₁ e₂ → beta_eq e₂ e₃ → beta_eq e₁ e₃

inductive valid_judgment_weak : Expr → Expr → Prop
  | k n                       : valid_judgment_weak SKM[K n] (.k (.mk n.succ))
  | s n                       : valid_judgment_weak SKM[S n] (.s (.mk n.succ))
  | m n                       : valid_judgment_weak SKM[M n] (.m (.mk n.succ))
  | call lhs rhs              : valid_judgment_weak SKM[(lhs rhs)] SKM[((M 0 lhs) (M 0 rhs))]

inductive valid_judgment : Expr → Expr → Prop
  | k n                       : valid_judgment SKM[K n] (.k (.mk n.succ))
  | s n                       : valid_judgment SKM[S n] (.s (.mk n.succ))
  | m n                       : valid_judgment SKM[M n] (.m (.mk n.succ))
  | call lhs rhs              : valid_judgment SKM[(lhs rhs)] SKM[((M 0 lhs) (M 0 rhs))]
  | beta_eq e t₁ t₂           : valid_judgment e t₁ → beta_eq t₁ t₂ → valid_judgment e t₂

end

/-
## Strong Normalization

A strong proof of consistency involves proving that every well-typed expression terminates. I do so. I utilize the typical reducibility candidates strategy.
-/

inductive sn : Expr → Prop
  | s        : sn s
  | k        : sn k
  | m        : sn m
  | trivial  : is_eval_once e e  → sn e
  | hard     : is_eval_once e e' → sn e' → sn e

/-
### Reducibility Candidates

Reducibility candidates. Noncomputable exprs are trivial.
A call is in `R(t)` if it produces an expression whose one-step reduxes are in `R`.
-/

inductive in_r_for : Expr → Expr → Prop
  | m              : in_r_for SKM[M n] (.m (.mk n.succ))
  | k              : in_r_for SKM[K n] (.k (.mk n.succ))
  | s              : in_r_for SKM[S n] (.s (.mk n.succ))
  | hard           : sn SKM[(lhs rhs)]
    → is_eval_once SKM[(lhs rhs)] e'
    → valid_judgment e' t
    → in_r_for e' t
    → in_r_for SKM[(lhs rhs)] t

/-
### Strong Normalization of Reducibility Candidates

This is pretty easy to prove. Just induction from the definition of `in_r_for`.
-/

lemma all_in_r_sn : ∀ e t, in_r_for e t → sn e := by
  intro e t h_in_r
  match h : e with
    | .s _ =>
      exact sn.s
    | .k _ =>
      exact sn.k
    | .m _ =>
      exact sn.m
    | SKM[(lhs rhs)] =>
      cases h_in_r
      case hard _ h _ _ _ =>
        exact h

/-
Note that we define evaluation as a relation on expressions. This is due to `eval_once`'s dependence on the type of `e`. This appears problematic and confusing. However, we can still prove membership in R of all well-typed expressions.
-/

lemma k_sn : sn (.k (.mk n)) := sn.k

lemma s_sn : sn (.s (.mk n)) := sn.s

lemma m_sn : sn (.m (.mk n)) := sn.m

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

As usual, we prove type preservation. We can speed up this process significantly by proving that all expressions are well-typed (e : M e).
-/

lemma all_well_typed_m_e : ∀ e, valid_judgment e SKM[(M 0 e)] := by
  intro e
  cases e
  case m m =>
    match m with
      | .mk n =>
        apply valid_judgment.beta_eq _ (.m (.mk n.succ))
        apply valid_judgment.m
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m
        apply valid_judgment.m
  case k k =>
    match k with
      | .mk n =>
        apply valid_judgment.beta_eq _ (.k (.mk n.succ))
        apply valid_judgment.k
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m
        apply valid_judgment.k
  case s s =>
    match s with
      | .mk n =>
        apply valid_judgment.beta_eq _ (.s (.mk n.succ))
        apply valid_judgment.s
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m
        apply valid_judgment.s
  case call c =>
    match c with
      | .mk lhs rhs =>
        have h_lhs_typed := @all_well_typed_m_e lhs
        have h_rhs_typed := @all_well_typed_m_e rhs
        apply valid_judgment.beta_eq _ SKM[((M 0 lhs) (M 0 rhs))]
        apply valid_judgment.call
        apply beta_eq.symm
        apply beta_eq.eval
        apply is_eval_once.m
        apply @valid_judgment.call _ _

/-
To prove preservation, we prove that we can derive typings for `(K (x : α) y : α)` from our base typing rules using `M`.

Note that our typing rules make extensive use of the `M` combinator for "reflection." We can use an `S`-transformation rule like such:

$$
(e_{1}\ e_{2} : M\ e_{1}\ e_{2}) \implies (e_{1}\ e_{2} : (M\ e_{1})\ (M\ e_{2}))
$$

This shortens our type preservation proof significantly by allowing us to collapse expressions of the form \\((M K arg)\\) to reducible \\((M K) (M arg)\\) expressions.
-/

namespace beta_eq

lemma m_distributes : beta_eq SKM[(M 0 (lhs rhs))] SKM[((M 0 lhs) (M 0 rhs))] := by
  apply beta_eq.eval
  apply is_eval_once.m
  apply @valid_judgment.call _ _

end beta_eq

namespace eval_once

lemma m_distributes : is_eval_once SKM[((M 0) (lhs rhs))] SKM[((M 0 lhs) (M 0 rhs))] := by
  apply is_eval_once.m
  apply valid_judgment.call

end eval_once

namespace valid_judgment

lemma m_distributes_judgment : valid_judgment SKM[(lhs rhs)] SKM[((M 0) (lhs rhs))] → valid_judgment SKM[(lhs rhs)] SKM[((M 0 lhs) (M 0 rhs))] := by
  intro h_t
  apply valid_judgment.beta_eq SKM[(lhs rhs)] SKM[((M 0) (lhs rhs))]
  exact h_t
  apply beta_eq.eval
  apply eval_once.m_distributes

end valid_judgment

lemma valid_judgment_m_iff : valid_judgment e t ↔ beta_eq SKM[(M 0 e)] t := by
  constructor
  intro h
  apply beta_eq.eval
  apply is_eval_once.m
  exact h
  intro h
  apply valid_judgment.beta_eq
  apply all_well_typed_m_e
  exact h

/-
I define a preservation helper for `K` evaluation.
-/

lemma weakening : valid_judgment_weak e t → valid_judgment e t := by
  intro h
  cases h
  case k =>
    simp [valid_judgment.k]
  case s =>
    simp [valid_judgment.s]
  case m =>
    simp [valid_judgment.m]
  case call lhs rhs =>
    simp [valid_judgment.call]

lemma congr_m : is_eval_once a b → beta_eq SKM[((M 0) a)] SKM[((M 0) b)] := by
  intro h
  apply beta_eq.trans
  apply beta_eq.right
  exact beta_eq.eval h
  exact beta_eq.rfl

lemma eval_preserves_judgment : ∀ c e' t, valid_judgment_weak c t → is_eval_once c e' → valid_judgment e' t := by
  intro c e' t h_t h_eval
  cases h_eval
  case k y n =>
    apply valid_judgment.beta_eq
    apply all_well_typed_m_e
    apply beta_eq.trans
    apply beta_eq.symm
    apply beta_eq.eval
    apply is_eval_once.k SKM[(M 0 e')] SKM[(M 0 y)]
    exact n
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.k
    cases h_t
    case a.a.a.call =>
      apply beta_eq.symm
      apply beta_eq.trans
      apply beta_eq.left
      apply beta_eq.m_distributes
      apply beta_eq.trans
      apply beta_eq.left
      apply beta_eq.left
      apply beta_eq.eval
      apply is_eval_once.m
      apply valid_judgment.k
      apply beta_eq.eval
      apply is_eval_once.k SKM[(M 0 e')] SKM[(M 0 y)] n.succ
  case s x y z n =>
    apply valid_judgment.beta_eq
    apply all_well_typed_m_e
    apply beta_eq.trans
    apply beta_eq.symm
    apply beta_eq.eval
    apply is_eval_once.right
    apply is_eval_once.s x y z
    exact n
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m
    apply weakening at h_t
    exact h_t
    exact beta_eq.rfl
  case m e'' h =>
    apply weakening at h_t
    apply valid_judgment_m_iff.mp at h_t
    apply valid_judgment_m_iff.mpr
    apply valid_judgment_m_iff.mp at h
    apply beta_eq.symm
    apply beta_eq.trans
    exact (beta_eq.symm h_t)
    apply beta_eq.trans
    apply beta_eq.right
    exact h
    exact beta_eq.rfl
  case left =>
    sorry
  case right =>
    sorry

lemma all_well_typed_in_r : ∀ e t, valid_judgment e t → in_r_for e t := by
  intro e t h_t
  match h : e with
    | .k _  =>
      cases h_t
      case beta_eq => sorry
      case k =>
        exact in_r_for.k
    | .s _ =>
      cases h_t
      case beta_eq => sorry
      case s =>
        exact in_r_for.s
    | .m _ =>
      cases h_t
      case beta_eq => sorry
      case m =>
        exact in_r_for.m
    | .call (.mk lhs rhs) =>
      cases h_t
      case beta_eq =>
        
        sorry
      case call =>
        have h_t_lhs : ∃ t_lhs, valid_judgment lhs t_lhs := sorry
        have h_t_rhs : ∃ t_rhs, valid_judgment rhs t_rhs := sorry

        obtain ⟨t_lhs, h_t_lhs⟩ := h_t_lhs
        obtain ⟨t_rhs, h_t_rhs⟩ := h_t_rhs

        have h_in_r_lhs := all_well_typed_in_r lhs t_lhs h_t_lhs
        have h_in_r_rhs := all_well_typed_in_r rhs t_rhs h_t_rhs

        have h_sn_lhs := all_in_r_sn lhs t_lhs h_in_r_lhs
        have h_sn_rhs := all_in_r_sn rhs t_rhs h_in_r_rhs

        match h₂ : e with
          | SKM[((K x) y)] =>
            simp_all
            obtain ⟨h_lhs_eq, h_rls_eq⟩ := h
            have h_in_r := @in_r_for.hard lhs rhs x (by
              rw [← h_lhs_eq]
              rw [← h_rls_eq]
              apply k_eval_sn
              have h_x_well_typed : valid_judgment_beta_eq x t := sorry
              have h_x_in_r := all_well_typed_in_r x t h_x_well_typed
              exact all_in_r_sn x t h_x_in_r
            ) (by
              rw [← h_lhs_eq]
              rw [← h_rls_eq]
              simp [is_eval_once.k]
            ) (by
              apply in_r_for.hard
              sorry
            )
          | SKM[(((S x) y) z)] => sorry
          | SKM[((M e) arg)] => sorry
          | _ => sorry

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
