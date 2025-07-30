/-
# SK Combinators

The [SK combinator calculus](https://en.wikipedia.org/wiki/SKI_combinator_calculus) is a turing-complete system of computation / logic without variables or scopes. SK programs are composed of two "combinators": \\(S\\) and \\(K\\). The semantics of \\(S\\) and \\(K\\) are given by:

$$
K x y = x \\\\
S x y z = x z (y z)
$$

The \\(K\\) combinator can be thought of as a "constant function maker." In lambda calculus, the \\(K\\) combinator is defined as:

$$
(\lambda a.(\lambda b.a))
$$

The \\(S\\) combinator can be thought of as a substitution function. It copies the argument \\(z\\), applies it to \\(x\\) and \\(y\\), then applies th results to each other.

The SK combinator calculus has been demonstrated to be turing-complete, and equivalent to the lambda calculus.

## Lean Examples

We can encode the combinators as dependent functions in Lean:
-/

import Mathlib.Tactic

def K {α : Type} {β : Type} (x : α) (_y : β) := x

def S {α : Type} {β : Type} {γ : Type} (x : α → β → γ) (y : α → β) (z : α) := x z (y z)

#eval K 0 1
-- => 0
#eval S (λx y => x + y) Nat.succ 1
-- => 3

/-
The SK combinators are turing complete. Dynamic evaluation of the combinators in a dependently typed language will invoke unfounded recursion, similarly to in the [lambda calculus](./SnLc.lean.md).

Strong normalization of the typed SK combinators has been comparatively under-studied compared to the simply typed lambda calculus. Furthermore, proofs of strong normalization of the dependently-typed SK combinators have yet to be mechanized in a language like Lean.

In this paper, I detail my interpretation of the combinators as dependently-typed functions, my representation of them in Lean, and my proof of their strong normalization in Lean.

-/
