/-
# Typing & Evaluation Rules

As described in the [intro](./Intro.lean.md) chapter, \\(M\\) enables more concise typing derivations for \\(K\\) and \\(S\\) through its own evaluation rules. The evaluation rules for \\(K\\) are quite clear, but \\(S\\) is more complex due to its dependent nature. To make prototyping easier, I will initially define the evaluation rules through a single-step reduction function.

Recall the types of \\(K\\) and \\(S\\) as defined earlier:

$$
K : \Pi (\alpha : \text{Type}) (\beta : \text{Type}) (x : \alpha) (y : \alpha), \alpha \\\\
S : \Pi (\alpha : \text{Type}) (\beta : \alpha \rightarrow \text{Type}) (\gamma : \alpha \rightarrow \text{Type}) \\\\ (x : \Pi (x : \alpha), \beta x \rightarrow \gamma x (\beta x)) (y : \Pi (x : \alpha), \beta x) (z : \alpha), \gamma x (\beta x)
$$

Our evaluation rules for \\(M K\\) and \\(M S\\) respectively ought to capture these typing rules.

## \\(M K\\) Evaluation Rules

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

# Type of \\(\Pi\\)

Note that in the type definition for \\(S\\), I refer to \\(\Pi\\) as a free-standing combinator. Thus, it must also well-typed. \\(\Pi\\) is also universe polymorphic with universe argument \\(m, n\\). Its first argument (\\(\alpha\\)) is of the form \\(\text{Type}\ m\\), while its second argument is a term of type \\(\alpha\\).

In the calculus of constructions, \\(\Pi\\) is typically typed like such:

$$
\frac{
\Gamma \vdash \alpha : \text{Type}\ n, y : \beta
}{
\Gamma \vdash (\Pi (x : \alpha), y) : \beta
}
$$

In our combinatory interpretation, \\(y\\) is further restricted such that it accepts an argument of type \\(\alpha\\). This mimicks variable substitution within \\(\Pi\\) without variables.

At the very least, we can say:

$$
\frac{
\Gamma \vdash \alpha : \text{Type}\ m,\ \beta : \text{Type}\ n, x : \alpha \rightarrow \beta
}{
\Gamma \vdash (\Pi\ \alpha\ \beta\ x) : (\alpha \rightarrow \beta)
}
$$

Clearly, \\(\Pi\\) accepts two \\(\text{Type}\\) arguments as parameters \\(\{\alpha, \beta\}\\) and a body with a type of the form \\(\alpha \rightarrow \beta\\).

I similarly make use of the \\(M\\) "reflection" construct to automate the mechanical formation of the type of \\(\Pi\\):

$$
M\ \Pi\ (\alpha \rightarrow \beta)\ x := \alpha \rightarrow \beta \\\\
\therefore \\\\
\frac{
\vdash \Pi : M\ \Pi,\ \Gamma \vdash \alpha : \text{Type}\ m,\\ \beta : \text{Type}\ n,\\ x : \alpha
}{
\Pi\ \alpha\ \beta\ x : \alpha \rightarrow \beta
}
$$

The judgment rules for \\(M\ \Pi\\) are as follows:

$$
\frac{
}{
\vdash M\ \Pi : \text{Type}\ m \rightarrow \text{Type}\ (succ\ 1)
}\\\\
\frac{
\Gamma \vdash \alpha : \text{Type}\ m,\ \beta : \text{Type}\ n,\ x : \alpha \rightarrow \beta
}{
\Gamma \vdash M\ \alpha\ \beta\ x : \text{Type}\ (m + n)
}
$$
-/

import SkLean.Ast

def eval_once : Expr → Option Expr
  | ⟪ (((((@K #_m) #_n) #_α) #_β) #x) #y ⟫ => pure x
  | ⟪ (((((@S #_m) #_n) #_o) #x) #y) #z ⟫ => pure ⟪ (#x #z) (#y #z) ⟫
  | ⟪ ((M ((@K #_m) #_n) #α)) #β ⟫ => pure ⟪ (#α) → ((#β) → (#α)) ⟫
  | ⟪ (((M (((@S #_m) #_n) #_o) #α) #β)) #γ ⟫ => pure ⟪ ((Π #α) (S (S (K ((Type _n) → (@Π #(max (max_universe _n) (max_universe _m)))) #β) (((((S #α) ((#α) → ((Type (max (max_universe γ).succ (max_universe α)).succ) → #α))) #γ) (((K ((#α) → ((Type (max (max_universe γ).succ (max_universe α)).succ) → #α))) #α) ((K (Type (max (max_universe γ).succ (max_universe α)).succ)) #α)) #γ)))) → ((Π (#α) (#β)) → (Π (#α) (S (#γ) (#β)))) ⟫
  | ⟪ ((Π #t_in) #body) #arg ⟫ => pure ⟪ (#body) (#arg) ⟫
  | _ => .none

