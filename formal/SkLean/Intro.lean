/-
# Intro

SK \\(\Pi\\) achieves dependent typing by introducing a \\(\Pi\\) combinator.

## The \\(\Pi\\) Combinator

The evaluation rules for \\(\Pi\\) are quite simple, and its interpretation as a dependent type formation rule are quite natural:

$$
(\Pi\ \alpha\ c)\ \text{arg} := c\ \text{arg} \\\\
\Pi\ \alpha\ c \cong \Pi(x : \alpha), c\ x
$$

To give a concrete example, a dependent \\(\text{Vec}\\) type may be represented as:

$$
\text{Vec} := \Pi\ \text{Type}\ (K\ (\Pi\ \mathbb{N}\ (K\ \text{Type}))) \\\\
$$

Here is an example reduction:

$$
\begin{align}
\text{Vec}\ \alpha\ n &= (\Pi\ \mathbb{N}\ (K\ \text{Type}))\ n \\\\
&= \text{Type}
\end{align}
$$

## Type of \\(\Pi\\)

Since \\(\Pi\\) is a free-standing object, it must be well-typed. Its type should be familiar. I define its type as such:

$$
\frac{
  \Gamma \vdash \alpha : T, \beta : T', x : \alpha
}{
  \Gamma \vdash \Pi \alpha \beta x : T' }
$$

By the evaluation rules for \\(\Pi\\), non-dependent types may be formed with \\(K\\), which discards the relevant argument, while \\(S\\) or \\(I\\) embed the argument within the body of the \\(\Pi\\)-type. For example, the expression \\(\Pi (x : \alpha), x\\) may be formed by the SK \\(\Pi\\) expression \\(\Pi\ \alpha\ I\\), where \\(I\\) is the identity combinator.

$$
\Pi (x : \alpha), x \cong \Pi\ \alpha\ I
$$

Note that, so far, I have been referring to the untyped varieties of \\(S\\), \\(K\\), and \\(I\\).

## SK Definitions

I follow the canonical evaluation rules for \\(K\\) and \\(S\\). However, I extend these rules to permit explicit type arguments to \\(K\\) and \\(S\\):

$$
K \alpha \beta x y :=  x \\\\
S \alpha \beta \gamma x y z := (x z) (y z)
$$

I interpret \\(K\\) and \\(S\\) in their dependently-typed forms as is typically done in the literature:

$$
K : \Pi (\alpha : \text{Type}) (\beta : \text{Type}) (x : \alpha) (y : \alpha), \alpha
$$

The dependent type of \\(S\\) is slightly more complicated:

$$
S : \Pi (\alpha : \text{Type}) (\beta : \alpha \rightarrow \text{Type}) (\gamma : \alpha \rightarrow \text{Type}) \\\\ (x : \Pi (x : \alpha), \beta x \rightarrow \gamma x (\beta x)) (y : \Pi (x : \alpha), \beta x) (z : \alpha), \gamma x (\beta x)
$$

I do not define \\(I\\) as a free-standing object in the theory. As has been demonstrated by [Schönfinkel](https://doi.org/10.1007/BF01448013), \\(I\\) may be derived using only \\(S\\) and \\(K\\).

Note that, thus far, I have been making use of the traditional \\(\Pi\\) notation. I give derivations of these types congruent with our evaluation rules and interpretation of \\(\Pi\\) as a combinator:

# Type Derivation Explosion

## K Combinator Type

In eta-expanded form, the evaluation mechanics of the type of \\(K\\) are clear:

$$
K \alpha \beta : \Pi\ \alpha (K (\Pi\ \beta (K \alpha))) \\\\
K \alpha \beta x y : (\Pi \beta (K \alpha)) \beta \\\\
K \alpha \beta x y : K \alpha y \\\\
K \alpha \beta x y : \alpha
$$

Ideally, the type of \\(K\\) ought to be point-free. Note that since \\(\alpha\\) appears twice in the type of \\(K \alpha \beta\\), surely \\(S\\) must be invoked:

$$
S\ \Pi\ \Pi\ \alpha = (\Pi \alpha) (\Pi \alpha)
$$

This derivation explodes quickly. The point-free type of \\(K\\) becomes very length without some additional construction. For brevity and correctness, I introduce an additional combinator, \\(M\\).

# The M Combinator

In order to keep the core of SK \\(\Pi\\) minimal and correct, I introduce \\(M\\). \\(M\\) is a "reflection" construction. That is, it represents the type of an expression. To avoid ambiguities, \\(M\\) cannot be constructed as a free-standing object, and may only be interpreted with an argument.

Here are the evaluation rules for \\(M\ K\\):

$$
M K \alpha \beta := \Pi \alpha (K (\Pi\ \beta (K \alpha)))
$$

In this way, \\(M K\\) captures the dependent type of \\(K\\) in a more concise manner. Since \\(M K\\) is a constructible object, it must also be well-typed. I define the type of \\(M K\\) like such:

$$
\frac{}
{\vdash M K : \Pi\ \text{Type}\ (K\ (\Pi\ \text{Type}\ \text{Type}))} \\\\
\frac{\Gamma \vdash \alpha : \text{Type}, \beta : \text{Type}}
{M K \alpha \beta : \text{Type}}
$$

Similarly, \\(M S\\) is defined to capture the dependent nature of \\(S\\) conveniently.

In the [next chapter](Ast.lean.md), I define an AST and DSL in Lean to encode our theory in a more formal manner.
-/
