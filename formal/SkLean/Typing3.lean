/-
# General Typing Rules

Note that, thus far, \\(\rightarrow\\), which we use to represent function types, is only interpretable for "non-dependent" functions. However, it is possible to represent the type of dependent functions using \\(\rightarrow\\). For example, take the identity function:

$$
id : \Pi_{x : A}, A \rightarrow A
$$

This could be represented in \\(SK(M)\\) as:

$$
id : S (\rightarrow) (SKS) \\\\
id\ \mathbb{N} : (\rightarrow\ \mathbb{N}) \mathbb{N}
$$

In general, we can say that a function call is well-typed if:

- Its left-hand side is of the type \\(K (M B) A B\\) and its right hand side is of the type \\(A\\)
- Application of the type of the left-hand side with the right-hand side expression is well-typed

I encode these judgment rules in Lean, making use of our derived typing for \\(\rightarrow\\). First, I define one-step evaluation for all combinators.
-/

import SkLean.LcSkmEta

inductive is_eval_once : Expr → Expr → Prop
  | k_call : is_eval_once SKM[((((K _α) _β) x) y)] x
  | s_call : is_eval_once SKM[((((((S _α) _β) _γ) x) y) z)] SKM[((x z) (y z))]
  | m_k    : is_eval_once SKM[(M K)] 

/-
bruh
-/
