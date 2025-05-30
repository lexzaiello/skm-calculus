/-
# Strong Normalization

In the previous chapter, we saw that:

- Lambda expressions can be evaluated using the "beta-reduction" rule
- Two lambda expressions can be said to be "beta-equivalent" (\\(=_{\beta}\\\)) if they are syntactically equivalent after some number of beta-reductions
- Some untyped expressions can potentially evaluate forever, which Lean doesn't like, and which prevents us from proving properties of our language, and programs written in our language.

## Termination: Constantly Decreasing Measure

In order to convince Lean that our evaluation function does not run on forever, we need to provide a constantly-decreasing measure whose value eventually causes termination. For example, we could provide a "steps" argument to our evaluation function which dictates a maximum bound on the number of steps in computing the expression:
-/

import SkLean.Lc
import Mathlib.Tactic

/-
First, we will extend our substitution function to our typed `Expr`:
-/

def with_indices_plus' (in_expr : Expr'') (shift_by : ℕ) : Expr'' :=
  match in_expr with
    | .abstraction bind_ty body =>
      .abstraction bind_ty (with_indices_plus' body shift_by.succ)
    | .var n =>
      if n > shift_by then
        .var (n + shift_by)
      else
        .var n
    | .app lhs rhs =>
      .app (with_indices_plus' lhs shift_by) (with_indices_plus' rhs shift_by)
    | x => x

def substitute'' (in_expr : Expr'') (n : ℕ) (with_expr : Expr'') : Expr'' :=
  match in_expr with
    | .abstraction bind_ty body =>
      .abstraction bind_ty (substitute'' body n.succ with_expr)
    | .var n' => if n == n' then with_indices_plus' with_expr n else .var n'
    | x => x

/-
We will naively terminate once we run out of steps:
-/

def eval_once (e : Expr'') : Expr'' :=
  match e with
  | .app (.abstraction _ body) rhs =>
    substitute'' body 0 rhs
  | .app lhs rhs =>
    .app (eval_once lhs) rhs
  | x => x

def eval''' (e : Expr'') (steps : ℕ) : Option Expr'' :=
  match steps with
    | 0 =>
      none
    | .succ n =>
      let e' := eval_once e

      if e' = e then
        some e'
      else
        eval''' e' n

/-
This is fine for some hand-written functions, like \\((\lambda x : \mathbb{N}.x) 1\\).
-/

#eval eval''' (.app (.abstraction (.base .nat) (.var 1)) (.cnst (.num 1))) 2

/-
However, with even simple expressions, we're limited to guessing and checking. We can do better.

## Definition of Strong Normalization

Assume that evaluation of a given expression \\(e\\) terminates. This is only true if there is some value for `steps` which can be provided to `eval'''`. Thus, we can say that:
-/

lemma exists_steps_terminates (terminates : Expr'' → Prop) :
  ∀ e, terminates e → ∃ n_steps, (eval''' e n_steps).isSome := sorry

/-
We can define "termination," or more strictly, "strong normalization" inductively as such:
-/

inductive Sn : Expr'' → Prop
  | trivial e : eval_once e = e → Sn e
  | hard    e : Sn (eval_once e)     → Sn e

/-
If the expression evaluates to itself after one step of evaluation, execution is complete, and it is strongly normalizing. In the recursive case, if it eventually reduces to itself after some sequence of reductions, it is also strongly normalizing.

Given this definition, we can refine our lemma. The proof is actually pretty easy:

- In the base case, the expression can be evaluated in one step.
- In the hard case:
  1. If `e` is strongly normalizing, then `eval_once e = e` is: **by induction** on the definition of `Sn`.
  2. Induction: successor of `steps e'`.

First, we  will prove (1):

In the reflexive case, we can prove the statement trivially by the definition of `Sn`.
-/

lemma eval_rfl_imp_sn_iff : ∀ e, eval_once e = e → (Sn (eval_once e) ↔ Sn e) := by
  intro e h_eq
  constructor
  rw [h_eq]
  simp
  rw [h_eq]
  simp

/-
Otherwise, `e ≠ eval_once e`, but clearly in all cases besides application, `eval_once e = e`.
In the application case, we do induction on each side of the bijection. `Sn (eval_once e) → Sn e` is trivially true per the .hard constructor of `Sn`.
`Sn e → Sn (eval_once e)` can be proven by pattern matching on `Sn e`.
-/

lemma sn_bidirectional : ∀ (e : Expr''), Sn (eval_once e) ↔ Sn e := by
  intro e
  match e with
    | .var n =>
      have h : eval_once (.var n) = (.var n) := by
        unfold eval_once
        simp
      apply eval_rfl_imp_sn_iff
      exact h
    | .cnst c =>
      have h : eval_once (.cnst c) = (.cnst c) := by
        unfold eval_once
        simp
      apply eval_rfl_imp_sn_iff
      exact h
    | .app lhs rhs =>
      constructor
      intro h
      apply Sn.hard
      exact h
      intro h
      cases h
      case mpr.trivial a =>
        rw [a]
        apply Sn.trivial
        exact a
      case mpr.hard a =>
        exact a
    | .abstraction bind_ty body =>
      have h : eval_once (.abstraction bind_ty body) = (.abstraction bind_ty body) := by
        unfold eval_once
        simp
      apply eval_rfl_imp_sn_iff
      exact h

/-
Using the fact that `Sn` is bidirectional (3), we can prove that strong normalization implies termination (2).
We simply obtain n_steps - 1 via induction given (3), and use its successor.
-/

lemma sn_imp_exists_steps : ∀ e, Sn e → ∃ n_steps, (eval''' e n_steps).isSome := by
  intro e h_sn
  induction h_sn
  use 1
  unfold eval''' at *
  simp
  case hard e' h h₂ =>
    have h_sn_e' := (sn_bidirectional e').mp h
    have ⟨n, h⟩ := h₂
    use n.succ
    unfold eval'''
    simp
    split
    case isTrue h_eq_eval =>
      simp
    case isFalse h_eval_some =>
      simp_all
  case h e' a =>
    simp [a]

/-
## Termination Proof

We have shown that every strongly normalizing expression terminates. Obviously, not all lambda calculus expressions are strongly normalizing (e.g., \\((\lambda x.x\ x)(\lambda x.x\ x)\\)). However, it has been extensively demonstrated that *welll-typed* expressions in the simply-typed lambda calculus (STLC) are strongly normalizing, and thus, terminate.

If we can prove that all expressions that are well-typed, given our inference rules in [chapter 1](./Lc.lean.md), are strongly normalizing, then we have successfully proven that all well-typed expressions terminate. Using our lemmas, we can extract a value for `steps`, and run our evaluation function successfully.

Termination proofs have been exhaustively enumerated for the STLC in the literature, even in Lean. However, proofs of strong normalization of other typed lambda calculi are currently of interest.

In this paper, I will be considering a particular class of type systems based on, "dependent types." The [next chapter](./CocLcExplainer.lean.md) details this subject.

-/
