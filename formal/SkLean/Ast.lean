/-
# Ast

SK \\(\Pi\\) achieves dependent typing by introducing a \\(\Pi\\) combinator. The evaluation rules for \\(\Pi\\) are quite simple, and its interpretation as a dependent type formation rule are quite natural:

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
-/

example : 1 = 1 := rfl

/-
End
-/
