/-
# Explicit, Dependent Typing of \\(K\\)

Using our definition of the \\(\rightarrow\\) expression, we can define a coherent typing of \\(K\\) that comports with our desired judgment rules.

To recap, I aim for \\(\rightarrow\\) to serve as a generalized representation of a function type. Recall that \\(\rightarrow\ A\ B\\) is defined as such:

$$
\rightarrow A B = K (M B) A B
$$

As we saw before, translation of the \\(\lambda\\)-calculus to \\(SK(M)\\) is possible. We can attempt to translate the \\(K\\) combinator as such:
-/

import SkLean.ArrowDef
import SkLean.LcSkmEta

def lc_dependent_k (u v : ℕ) : LExpr := (.lam (.ty u) (.lam (.ty v) (.lam (.var 1) (.lam (.var 2) (.var 1)))))

#eval lc_dependent_k 0 0 |> (lift [] .)

/-
However, we will have issues with translating variables inside types. For now, we can hand-encode the typing of \\(K\\).
Note that I omit explicit type parameters in calls to the combinators in some places. These will be revealed in a further translation.

$$
K\ \mathbb{N}\ \mathbb{R} : (\rightarrow \mathbb{N}\ (\rightarrow \mathbb{R}\ \mathbb{N})) \\\\
K\ \mathbb{N}\ \mathbb{R} : S \rightarrow (\rightarrow \mathbb{R})\ \mathbb{N}
$$

Using \\(\lambda\\)-abstraction, we can easily lift the \\(\\mathbb{R}\\):

$$
K\ \mathbb{N}\ \mathbb{R} : (\lambda r.S \rightarrow (\rightarrow r)\)\ \mathbb{R}\ \mathbb{N} \\
$$

Following the \\(S\\)-transformation rule:

$$
K\ \mathbb{N}\ \mathbb{R} : (\lambda r.(S \rightarrow) (\rightarrow r)\)\ \mathbb{R}\ \mathbb{N} \\\\
K\ \mathbb{N}\ \mathbb{R} : (S (\lambda r.(S \rightarrow) (\lambda r.(\rightarrow r))\)\ \mathbb{R}\ \mathbb{N} \\\\
K\ \mathbb{N}\ \mathbb{R} : (S (K\ (S \rightarrow) (S ((K \rightarrow) (SKS)))\)\ \mathbb{R}\ \mathbb{N} \\\\
$$

More explicitly in Lean using \\(\lambda\\)-transformation:
-/

def lc_type_bad (u v : ℕ) : LExpr := (.lam (.ty u) (.lam (.ty v) (.call (.call (.raw arrow₀) (.var 1)) (.call (.call (.raw arrow₀) (.var 0)) (.var 1)))))


#eval lc_type_bad 0 0 |> (lift [] . >>= to_sk >>= (fun e => parse_arrow $ eval_n 20 SKM[((e K) S)]))
