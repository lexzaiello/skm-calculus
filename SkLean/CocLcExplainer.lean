/-
# Dependent Typing

In the previous two chapters, we saw that adding types to the lambda calculus enables well-founded, provably terminating reduction.

However, our type system is terse and inflexible. "Polymorphism" is a common feature in most programming languages which enables reuse of logic across types. This is not possible in our simply-typed lambda calculus at the expression-level.

For example, to create a generic identity function that works with \\(\mathbb{R}\\) and \\(\mathbb{N}\\), we would have to duplicate the function:
-/

import SkLean.Lc
import SkLean.SnLc

open Expr''

def id₁ := abstraction (.base .nat) (.var 1)

/-
We can see that the expression `(λ (x : ℕ).x) (1 : ℝ)` does not type-check:
-/

#eval type_of [] (app id₁ (.cnst (.int 0)))
-- => None

/-
An alternative solution is to modify our type system such that the type of a term can depend on another term.

For example, a dependent identity function:
-/

def myid (α : Type) (x : α) : α := x

/-
Type systems of this kind have numerous advantages, enabling highly expressive code, and forming the basis for modern theorem-proving software.

One such type system is the [calculus of constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions) (CoC). At the term level, the CoC is very similar to the simply typed lambda calculus: it has variables, abstractions, function application, and beta reduction.

The CoC enables its style of polymorphism through type-level substitution. Where the type of a lambda abstraction in the STLC is of the form \\(\alpha \rightarrow \beta\\), in the CoC it is of the form \\(\forall x : \alpha.\beta\\). The \\(\forall\\) expression behaves similarly to a lambda abstraction, in that it can have values substituted in for its binder \\(x\\).

The full grammar of the CoC is informally given by:

$$
e ::= \text{Prop}\ |\ \text{Type}\ n\ |\ x\ |\ \forall x : e.e\ |\ \lambda x : e.e\ |\ e\ e
$$

The type inference rules for the CoC are informally given by:

- \\(\text{Prop}\\) is of type \\(\text{Type 0}\\).
- \\(\text{Type}\ n\\) is of type \\(\text{Type n + 1}\\)
- Variable \\(x\\) is of type \\(t\\) if \\(t\\) is the type of its binder in the context
- \\(\forall x:tx.b\\) is of type \\(tb\\) where \\(tb\\) is the type of \\(b\\)
- \\(\lambda x : tx.b\\) is of type \\(\forall x : tx.tb\\) where \\(tb\\) is the type of \\(b\\)
- \\(e\\) is of type \\(t'\\) if \\(e\\) is of type \\(t\\) and \\(t'\\) is beta-equivalent to \\(t\\)

The [next chapter]

-/
