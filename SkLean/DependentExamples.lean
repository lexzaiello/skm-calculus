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

`M` is basically the `S` combinator, but lhs is the body and rhs is the type signature. This allows higher-kinded type-expr composition. This makes the combinators fully dependently-typed.

```
def M : (∀ x : A, B x) := sorry
mything : (?1 : Type → Type) := (?2 : Type → Type → Type)
M mything ℕ := ?2 ℕ (?1 ℕ)
```

Notably, this allows us to fully eliminate binders in all types.
We can simplify our type system using a notion of a "valid transition." `K`, `S`, and `M` are well-typed on their own. They are parametric over some types, respectively.
Application is entirely what assigns meaning to these expressions. We **do not** need variables, substitution, or `∀` to express this.
-/

begin mutual

inductive M where
  | mk : M
deriving Repr

inductive S where
  | mk : S
deriving DecidableEq, Repr, BEq

inductive K where
  | mk : K
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

mutual

def sizeOfC (c : Call) : ℕ :=
  match c with
    | .mk lhs rhs => 2 + (sizeOf lhs) + (sizeOf rhs)

def sizeOf (e : Expr) : ℕ :=
  match e with
    | .m _ => 1
    | .s _ => 1
    | .k _ => 1
    | .call c => sizeOfC c

end

/-
## DSL

We make use of a small DSL for legibility.
-/

declare_syntax_cat skmexpr
syntax "K"             : skmexpr
syntax "S"             : skmexpr
syntax "M"             : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax ident           : skmexpr
syntax "(" skmexpr ")" : skmexpr

syntax " ⟪ " skmexpr " ⟫ " : term

macro_rules
  | `(⟪ K ⟫)                      => `(Expr.k .mk)
  | `(⟪ S ⟫)                      => `(Expr.s .mk)
  | `(⟪ M ⟫)                      => `(Expr.m .mk)
  | `(⟪ $e:ident ⟫)               => `($e)
  | `(⟪ ($e:skmexpr) ⟫)           => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫) => `(Expr.call (.mk ⟪ $e₁ ⟫ ⟪ $e₂ ⟫))

syntax "SKM[ " skmexpr " ] " : term

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
M\ (x : t)\ \text{arg} = x\ \text{arg}\ (t\ \text{arg}) \\\\
M\ K\ \mathbb{N} = K\ \mathbb{N}\ (K\ \mathbb{N}) = \mathbb{N} \\\\
M\ K\ K = K\ K\ (K\ K) = K \\\\
\frac{
  \Gamma \vdash e : ?, arg : t, (M\ e\ \text{arg} : t_{2})
}{
  \Gamma \vdash ? = t, e : t
}
$$
-/

mutual

inductive is_eval_once : Call → Expr → Prop
  | k x y     : is_eval_once (.mk SKM[(K x)] y) x
  | s x y z   : is_eval_once (.mk SKM[((S x) y)] z) SKM[((x z) (y z))]
  | m e t arg : valid_judgment e t → is_eval_once (.mk SKM[(M e)] arg) SKM[((e arg) (t arg))]
  | rfl       : (.call c) = e₂ → is_eval_once c e₂

inductive beta_eq : SkExpr → SkExpr → Prop
  | rfl                       : e₁ = e₂            → beta_eq e₁ e₂
  | hard    e₁ (e₂ : Call) e₃ : is_eval_once e₂ e₃ → beta_eq e₁ e₃ → beta_eq e₁ (.call e₂)
  | symm                      : beta_eq e₂ e₁ → beta_eq e₁ e₂
  | trans                     : beta_eq e₁ e₂ → beta_eq e₂ e₃ → beta_eq e₁ e₃

inductive valid_judgment : Expr → Expr → Prop
  | k                    : valid_judgment SKM[K] SKM[K]
  | s                    : valid_judgment SKM[S] SKM[S]
  | m                    : valid_judgment SKM[M] SKM[M]
  | call lhs rhs         : valid_judgment (.call (.mk lhs rhs)) SKM[((M lhs) rhs)]

inductive valid_judgment_beta_eq : Expr → Expr → Prop
  | beta_eq e t₁ t₂      : valid_judgment_beta_eq e t₁ → beta_eq t₁ t₂ → valid_judgment_beta_eq e t₂

end

/-
## Consistency

In order to prove consistency of our type system, we need to demonstrate that no false statement can be constructed (thus, proving false). First, we will need to define `False` and `True`.
We will defer to the standard definition of `false` in combinatory logic:
-/

mutual

partial def type_of (e : Expr) : Expr :=
  match e with
    | SKM[K] => SKM[K]
    | SKM[S] => SKM[S]
    | SKM[M] => SKM[M]
    | .call (.mk lhs rhs) => eval SKM[((M lhs) rhs)]

partial def eval (e : Expr) : Expr :=
  match e with
    | SKM[((K x) _y)] => x
    | SKM[(((S x) y) z)] => eval SKM[((x z) (y z))]
    | SKM[((M e) arg)] =>
      let t_e := type_of e

      eval SKM[((e arg) (t_e arg))]
    | x => x

end

def flse := SKM[(S K)]
def true := SKM[K]

/-
We can prove consistency if we cannot construct an expression that occupies the type `flse`. A trivial case to attempt is the judgment `flse : flse`. If this holds from our judgment rules, we are cooked.
-/

lemma eval_once_imp_beta_eq : ∀ e e', is_eval_once e e'→ beta_eq (.call e) e' := by
  intro e e' h_eval
  apply beta_eq.symm
  apply beta_eq.hard _ e e'
  exact h_eval
  simp [beta_eq.rfl]

lemma call_self_not_eval_once : ∀ e, ¬ is_eval_once (.mk e e) e := by
  intro e h
  cases h
  case rfl h =>
    cases e
    case m m =>
      simp_all
    case k =>
      simp_all
    case s =>
      simp_all
    case call c =>
      simp_all
      apply_fun sizeOfC at h
      simp [sizeOfC] at h
      ring_nf at h
      simp [_root_.sizeOf, sizeOfC] at h
      linarith

example : ¬(valid_judgment flse flse) := by
  intro a
  rw [flse] at *
  cases a

lemma no_one_step_occupies_false : ∀ e, ¬ (valid_judgment e flse) := by
  intro e h
  cases h

/-
We can expand our lemma to beta-equivalence up to some number of steps.
-/
inductive occupies_false : ℕ → Expr → Prop
  | trivial   : valid_judgment e flse → occupies_false 0 e
  | hard e e' : is_eval_once e e'     → occupies_false n e' → occupies_false n.succ (.call e)

lemma no_one_step_occupies_false' : ∀ e, ¬ occupies_false 0 e := by
  intro e h
  cases h
  case trivial h =>
    cases h

lemma no_two_step_occupies_false : ∀ e, ¬ occupies_false 1 e := by
  intro e h
  cases h
  case hard e' t h_valid =>
    simp [no_one_step_occupies_false'] at h_valid

/-
Not 100% sure what happened here, but yay?
-/

lemma no_n_step_occupies_false : ∀ e n, ¬ occupies_false n e := by
  intro e n h
  induction h
  case trivial e' h =>
    cases h
  case hard n' e t h_t_valid=>
    exact h_t_valid

/-
## Strong Normalization

A stronger proof of consistency involves proving that every well-typed expression terminates. I do so. I utilize the typical reducibility candidates strategy.
-/

inductive sn : Expr → Prop
  | s        : sn s
  | k        : sn k
  | m        : sn m
  | trivial  : is_eval_once e (.call e)  → sn (.call e)
  | hard     : is_eval_once e e'         → sn e' → sn (.call e)

/-
### Reducibility Candidates

Reducibility candidates. Noncomputable exprs are trivial.
A call is in `R(t)` if it produces an expression whose one-step reduxes are in `R`.
-/

inductive in_r_for : Expr → Expr → Prop
  | m              : in_r_for SKM[M] SKM[M]
  | k              : in_r_for SKM[K] SKM[K]
  | s              : in_r_for SKM[S] SKM[S]
  | hard           : sn SKM[(lhs rhs)]
    → is_eval_once (.mk lhs rhs) e'
    → in_r_for e' SKM[((M lhs) rhs)]
    → in_r_for SKM[(lhs rhs)] SKM[((M lhs) rhs)]

/-
### Strong Normalization of Reducibility Candidates

This should be pretty hard to prove.
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
    | .call (.mk lhs rhs) =>
      cases h_in_r
      case hard _ h _ _ =>
        exact h


