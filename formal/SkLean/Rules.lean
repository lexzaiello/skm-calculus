/-
# Typing & Evaluation Rules

As described in the [intro](./Intro.lean.md) chapter, \\(M\\) enables more concise typing derivations for \\(K\\) and \\(S\\) through its own evaluation rules. The evaluation rules for \\(K\\) are quite clear, but \\(S\\) is more complex due to its dependent nature. To make prototyping easier, I will initially define the evaluation rules through a single-step reduction function.

Recall the types of \\(K\\) and \\(S\\) as defined earlier:

$$
K : \Pi (\alpha : \text{Type}) (\beta : \text{Type}) (x : \alpha) (y : \alpha), \alpha \\\\
S : \Pi (\alpha : \text{Type}) (\beta : \alpha \rightarrow \text{Type}) (\gamma : \alpha \rightarrow \text{Type}) \\\\ (x : \Pi (x : \alpha), \beta x \rightarrow \gamma x (\beta x)) (y : \Pi (x : \alpha), \beta x) (z : \alpha), \gamma x (\beta x)
$$

Our evaluation rules for \\(M K\\) and \\(M S\\) respectively ought to capture these typing rules.

## \\(M K\\) Evalutaion Rules

Note that since \\(K\\) requires explicit type arguments, defining a type rule for \\(K\\) without \\(M K\\) would be impossible. The type argument \\(\alpha\\) needs to be duplicated, and this is only possible with \\(S\\), but \\(S\\) also requires explicit type arguments. Thus, \\(M K\\) simplifies matters significantly.

$$
M K \alpha \beta := \Pi\ \alpha\ (K\ \alpha\ (\Pi\ \beta\ (K\ \beta\ \alpha)))
$$

## \\(M S\\) Evaluation Rules

The evaluation rules for \\(M S\\) are less clear, since \\(S\\) is truly dependent. To simplify matters, we may first type each argument \\(x, y, z\\) separately.

In standard \\(\Pi\\) notation:

$$
x : \Pi (x : \alpha), \beta x \rightarrow \gamma x (\beta x) \\\\
y : \Pi (x : \alpha), \beta x \\\\
z : \Pi (x : \alpha), \gamma x (\beta x)
$$

The argument \\(y\\) is clearly the simplest of them. We may type it in combinatory \\(\Pi\\) notation as such:

$$
y : \Pi \alpha \beta \\\\
y x = \beta x
$$

\\(x\\) is slightly more complicated, due to needing explicit type arguments in the call to \\(S\\) for duplicating x. I will consider the untyped variation of \\(S\\) first for simplicity:

$$
x : \Pi\ \alpha (S (S (K\ \Pi) \beta) (S \gamma \beta) \\\\
x z : \Pi (\beta z) (\gamma z (\beta z))
$$

Note that since the body of the type of \\(x\\) is not a \\(\Pi\\) expression, but an \\(\rightarrow\\) expression, we need to insert an additional \\(K\\) expression.

$$
\begin{align}
x z &: \Pi (\beta x) (K (\gamma x)) \\\\
x &: \Pi\ \alpha\ (S (S (K\ \Pi) \beta) (S (K K) \gamma))
\end{align}
$$

The final consequent in the type of \\(S\\), which I refer to as \\(z\\) may be defined as such:

$$
z : \Pi \alpha (S \gamma \beta) \\\\
z x : \gamma x (\beta x)
$$

Putting it all together:

$$
M S \alpha \beta \gamma := (\Pi\ \alpha\ (S (S (K\ \Pi) \beta) (S (K K) \gamma))) \rightarrow (\Pi \alpha \beta) \rightarrow (\Pi \alpha (S \gamma \beta))
$$
-/
