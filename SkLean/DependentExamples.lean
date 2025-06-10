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
  | k x y        : is_eval_once (.mk SKM[(K x)] y) x
  | s x y z      : is_eval_once (.mk SKM[((S x) y)] z) SKM[((x z) (y z))]
  | m e t arg    : valid_judgment e t    → is_eval_once (.mk SKM[(M e)] arg) SKM[((e arg) (t arg))]
  | call lhs rhs : is_eval_once lhs lhs' → is_eval_once (.mk lhs' rhs) e' → is_eval_once (.mk (.call lhs) rhs) e'
  | rfl          : (.call c) = e₂ → is_eval_once c e₂

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
  | trivial              : valid_judgment e t → valid_judgment_beta_eq e t
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
    | .call (.mk lhs rhs) =>
      cases h_in_r
      case hard _ h _ _ =>
        exact h

/-
Note that we define evaluation as a relation on expressions. This is due to `eval_once`'s dependence on the type of `e`. This appears problematic and confusing. However, we can still prove membership in R of all well-typed expressions.
-/

lemma k_sn : sn (.k .mk) := sn.k

lemma s_sn : sn (.s .mk) := sn.s

lemma m_sn : sn (.m .mk) := sn.m

lemma k_eval_sn : ∀ x y, sn x → sn SKM[((K x) y)] := by
  intro x y sn_x
  apply @sn.hard (.mk SKM[(K x)] y) x
  simp [is_eval_once.k]
  exact sn_x

lemma s_eval_sn : ∀ x y z, sn SKM[((x z) (y z))] → sn SKM[(((S x) y) z)] := by
  intro x y z sn_eval
  apply @sn.hard (.mk SKM[((S x) y)] z) SKM[((x z) (y z))]
  simp [is_eval_once.s]
  exact sn_eval

/-
## Type Preservation

As usual, we prove type preservation.
-/

lemma eval_preserves_judgment : ∀ c e' t, valid_judgment (.call c) t → is_eval_once c e' → valid_judgment_beta_eq e' t := by
  intro c e' t h_t h_eval
  cases h_eval
  case k y =>
    cases h_t
    case call =>
      cases e'
      case m m =>
        match m with
          | .mk =>
            apply valid_judgment_beta_eq.beta_eq (.m .mk) (.m .mk) (Expr.call (Call.mk (Expr.call (Call.mk (Expr.m .mk) (Expr.call (Call.mk (Expr.k .mk) (Expr.m .mk))))) y))
            exact valid_judgment_beta_eq.trivial (by apply valid_judgment.m)
            apply beta_eq.hard
            apply is_eval_once.m
            apply valid_judgment.call
            apply beta_eq.hard
            -- (((K M) y) (((M K) M) y))
            -- => M (((M K) M) y)
            -- => M ((K M (K M)) y)
            -- => M (M y)
            -- => M (M y) : M
            have h := is_eval_once.k SKM[M] y
            
            sorry
      case k => sorry
      case s => sorry
      case call => sorry
  case s x' y z => sorry
  case m => sorry
  case rfl =>
    simp_all

lemma all_well_typed_in_r : ∀ e t, valid_judgment_beta_eq e t → in_r_for e t := by
  intro e t h_t
  match h : e with
    | .k _  =>
      cases h_t
      case beta_eq => sorry
      case trivial t' h_t_inner =>
        cases h_t_inner
        case k =>
          exact in_r_for.k
    | .s _ =>
      cases h_t
      case beta_eq => sorry
      case trivial t' h_t_inner =>
        cases h_t_inner
        case s =>
          exact in_r_for.s
    | .m _ =>
      cases h_t
      case beta_eq => sorry
      case trivial t' h_t_inner =>
        cases h_t_inner
        case m =>
          exact in_r_for.m
    | .call (.mk lhs rhs) =>
      cases h_t
      case beta_eq =>
        
        sorry
      case trivial h_t_inner =>
        have h_t_lhs : ∃ t_lhs, valid_judgment_beta_eq lhs t_lhs := sorry
        have h_t_rhs : ∃ t_rhs, valid_judgment_beta_eq rhs t_rhs := sorry

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
