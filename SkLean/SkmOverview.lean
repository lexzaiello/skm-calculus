/-
# Overview

Translation strategies from the \\(\lambda\\)-calculus to SK have been exhaustively enumerated.
By adding one combinator, \\(M (e : t) = t\\), the calculus of constructions can be translated to \\(SK(M)\\).

## The \\(M\\) Combinator

\\(M\\) serves as a "reflection" combinator (\\(M\\) for meta).

$$
M\ (e : t) = t
$$

In this way, there is a "canonical" type for every \\(e\\) that is well-typed.
\\(M\\) is polymorphic, and not parametrically typed.

## Explicit Typing of \\(S\\) and \\(K\\)

I extend the \\(S\\) and\\(K\\) combinators with explicit typing while preserving their original meaning.

$$
S \alpha \beta \gamma x y z = (x z) (y z) \\\\
K \alpha \beta x y = x
$$

### \\(M\\) Typing

$$
(M (e : t) : M t) \\\\
(M (e : t) : M (M e))\\\\
M : S (KM) M \\\\
M e : M (M e)
$$

Note that the input type of \\(M\\) is not readily interpretable here. We can generalize to say that a function call is well-typed the application of its argument to the function's type produces some normal form and makes "progress".
This comports with our definition of "types" as expressions which are well-typed, but which do not make progress.
This definition avoids circular reasoning, since evaluation rules for M, S, and K are defined separately from judgment rules.

For example, these expressions are well-typed, but do not make progress:

$$
K\ \alpha\ \beta (x : \alpha) \\\\
S\ \alpha\ \beta\ \gamma (x : \alpha)
$$

Thus, we can encode the notion of a "valid" judgment structurally through this notion of progress.

While evaluation of \\(K x y\\) is always defined, calls to \\(K\\) ought not type-check unless its first argument also typechecks.
It suffices, then to say that:

$$
K : S M (K M) \\\\
K \alpha \beta (x : \alpha) : \text{Type} \\\\
K \alpha \beta (x : \alpha) (y : \beta) : M x \\\\
$$

We need some way for \\(K\\) calls to not typecheck for arguments that do not produce a normal form (i.e., ones that produce type \\(\text{Type}\\)).
Recall that our rule for function calls says that a function call \\((e_{1} : t)\ e_{2}\\) is well-typed if \\(t\ e_{2}\\) makes progress and is well-typed.
An expression has type \\(\text{Type}\\) if it is well-typed and makes no progress. Therefore, \\(K \alpha \beta : \text{Type}\\). \\(K \alpha \beta\\) is well-typed
However, \\(\text{Type}\\) is well-typed and makes no progress, yet its type is not \\(\text{Type}\\).

$$
K \alpha \beta (x : \alpha) : K\ \text{Type}\ \text{Type}\ (\alpha : \text{Type}\)
$$

$$
K : K \text{Type} \text{Type} \\\\
$$

#### What about input types?



$$
\rightarrow\ A\ B\ (x : A)\ = B \\\\
\rightarrow := S (K M)
\rightarrow A B = S (K M) A B = (K M B) (A B) = M (A B)
$$

Note that this expression still relies on the \\(\lambda\\) abstraction and contains variables. We will see later that this expression is derivable fully point-free using a translation algorithm from the CoC to \\(SK(M)\\).

#### Type of \\(\rightarrow\\)

\\(\rightarrow\ A\ B\\) should be well-typed for any inputs \\(A\\) and \\(B\\) which are also types. But what are "types" in our language? Obviously \\(\rightarrow\ A\ B\\) is a type. If we can identify the universe of things described similarly to \\(\rightarrow\ A\ B\\), then we can assign the type \\(\text{Type}\\) to them. Assuming the existence of such a type (stratified by universes to prevent paradoxes), then \\(\rightarrow\\) is typed as such:

$$
\rightarrow : \text{Type} \rightarrow (\text{Type} \rightarrow \text{Type})
$$

This appears circular. However, inline, \\(\eta\\)-expanded calls to \\(\rightarrow\\) have an obvious, immediate representation, as defined above.

Obviously, expressions of the form \\(\rightarrow\ A\ B\\) are of type \\(\text{Type}\\). Notably, it appears that all expressions of type \\(\text{Type}\\) are noncomputable. That is, they are well-typed, yet make no progress.

### Non-Dependent Function Application Judgment Rule

Using our definition of \\(\rightarrow\\) and assuming that all "callable" expressions have some type of the form \\(A\ \rightarrow\ B\\), we can define a judgment rule:

$$
\frac{M : (A \rightarrow B),\ N : A}{\Gamma \vdash M N : B}
$$

However, we can generalize using our expansion of \\(\rightarrow\\) assuming that the type of any function is an expression which, when supplied an argument of its input type, produces an output type:

$$
\frac{M : t,\ N : e,\ (t\ e : t') = e'}{\Gamma \vdash M N : e'}
$$

We can say that **any function call is well-typed if**:

- Its left-hand side (\\(e_{0}\\)) is well-typed with type \\(t_{0}\\)
- Its right-hand side (\\(e_{1}\\)) is well-typed with type \\(t_{1}\\)
- \\(t_{0}\ e_{1}\\) is well-typed with type \\(t'\\)

We conclude that the type of the entire expression is \\(t'\\).

### Dependent Function Types using \\(S\\) and \\(\rightarrow\\)

\\(K\\) is dependent, and we cannot express its type similarly to in Lean with just \\(\rightarrow\\). However, as we will see later, \\(\rightarrow\\) is point-free, and expands to an expression containing computable \\(S\\), \\(K\\), and \\(M\\) expressions. In the type of \\(K : \alpha \rightarrow \beta \rightarrow \alpha\\), the input type \\(\alpha\\) is copied. An obvious candidate for translation is:

$$
K : S\ \rightarrow\ \rightarrow \\\\
K\ \alpha\ \beta : ((\rightarrow \alpha\ (\rightarrow \alpha))\ \beta)
$$

This is not exactly what we need. \\(\beta\\) should be the second argument to the inenr \\(\rightarrow\\) call. We can lift this expression to achieve this. We will do so using the well-established method of translation from the untyped \\(\lambda\\)-calculus to \\(SK\\).

In the next chapter, I utilize the typical translation from the \\(\lambda\\)-calculus to \\(SK\\) to make our \\(\rightarrow\\) expression and typign of \\(K\\) point-free.

-/
