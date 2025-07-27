/-
# Overview

Translation strategies from the \\(\lambda\\)-calculus to SK have been exhaustively enumerated.
By adding one combinator, \\(M (e : t) = t\\), the calculus of constructions can be translated to \\(SK(M)\\).

## The \\(M\\) Combinator

\\(M\\) serves as a reflection combinator (\\(M\\) for meta).

$$
M\ (e : t) = t
$$

In this way, there is a "canonical" type for every \\(e\\) that is well-typed.
\\(M\\) is polymorphic, and not parametrically typed.

## The \\(\rightarrow\\) Expression

Using only \\(S\\) ,\\(K\\) and \\(M\\), we can define an expression interpretable as the type of a function (e.g, \\(A \rightarrow B\\). This expression is called \\(\rightarrow\\).

\\(\rightarrow A B\\) represents the type of a function taking in expressions of type \\(A\\) as inputs and outputting expressions of type \\(B\\) as outputs.

Note that since \\(\rightarrow\\) is an expression, it can be computed with.

### Example typing: Dependent `I` Combinator

Although `I` is not defined in the core \\(SK(M)\\) calculus, it can be derived from \\(S\\) and \\(K\\).
The typing of \\(I\\) is usually of the form \\(I : \forall (t : \text{Type}), t \rightarrow t\\). We can model this typing in the \\(SK(M)\\) calculus as such:

$$
I : S \rightarrow (S K K)
$$

Note that in general, nondependent functions are of the type:

$$
e : A \rightarrow B \approximate e : K (\rightarrow A B)
$$

### \\(\rightarrow\\) Definition

In practice, \\(\rightarrow\\) is defined as a Church-encoded pair.

$$
\rightarrow := ((S (K ((S (K S)) K))) K)
$$

### Interpretation of Function Types

Using our definition of the \\(\rightarrow\\) expression, we can define judgment rules for function application.
In general, a function call \\(e_{1}\ e_{2}\\) is well-typed if:

- Its left hand side is of the form:
  - \\(e_{1} : K (\rightarrow A B)\\) in the non-dependent case
  - \\(e_{1} : S \rightarrow f\\) in the dependent case
- The expression 

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
