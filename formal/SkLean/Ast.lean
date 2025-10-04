/-
# Ast

SK \\(\Pi\\) achieves dependent typing by introducing a \\(\Pi\\) combinator.

## The \\(\Pi\\) Combinator

The evaluation rules for \\(\Pi\\) are quite simple, and its interpretation as a dependent type formation rule are quite natural:

$$
(\Pi\ \alpha\ c)\ \text{arg} \to c\ \text{arg} \\\\
\Pi\ \alpha\ c \cong \Pi(x : \alpha), c\ x
$$

To give a concrete example, a dependent \\(\text{Vec}\\) type may be represented as:

$$
\text{Vec} := \Pi\ \text{Type}\ (K\ (\Pi\ \mathbb{N}\ (K\ \text{Type}))) \\\\
$$

Here is an example reduction:
$$
\begin{align}
\text{Vec}\ \alpha\ n &\to (\Pi\ \mathbb{N}\ (K\ \text{Type}))\ n \\\\
&\to \text{Type}
\end{align}
$$

By the evaluation rules for \\(\Pi\\), non-dependent types may be formed with \\(K\\), which discards the relevant argument, while \\(S\\) or \\(I\\) embed the argument within the body of the \\(\Pi\\)-type. For example, the expression \\(\Pi (x : \alpha), x\\) may be formed by the SK \\(\Pi\\) expression \\(\Pi\ \alpha\ I\\), where \\(I\\) is the identity combinator.

$$
\Pi (x : \alpha), x \cong \Pi\ \alpha\ I
$$

Note that, so far, I have been referring to the untyped varieties of \\(S\\), \\(K\\), and \\(I\\).

## SK Definitions

I follow the canonical evaluation rules for \\(K\\) and \\(S\\). However, I extend these rules to permit explicit type arguments to \\(K\\) and \\(S\\):

$$
K \alpha \beta x y\to x \\\\
S \alpha \beta \gamma x y z \to (x z) (y z)
$$

I interpret \\(K\\) and \\(S\\) in their dependently-typed forms as is typically done in the literature:

$$
K : \Pi (\alpha : \text{Type}) (\beta : \text{Type}) (x : \alpha) (y : \alpha), \alpha
$$

The dependent type of \\(S\\) is slightly more complicated:

$$
S : \Pi (\alpha : \text{Type}) (\beta : \alpha \rightarrow \text{Type}) (\gamma : \alpha \rightarrow \text{Type}) \\\\ (x : \Pi (x : \alpha), \beta x \rightarrow \gamma x) (y : \Pi (x : \alpha), \beta x) (z : \alpha), \gamma x
$$


-/

example : 1 = 1 := rfl

/-
End
-/
