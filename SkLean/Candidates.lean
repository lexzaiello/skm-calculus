/-
# Reducibility Candidates

I extend existing proofs of strong normalization of the STLC and simply-typed SK combinators by utilizing Girard's "reducibility candidates."

I define reducibility candidates as expressions which are [hereditarily terminating](https://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/tait.pdf):

- In the case of unevaluable expressions, the expression is trivially hereditarily terminating.
- In the case of function application (\\e_{1}\ e_{2}\\), an expression is said to be hereditarily terminating if
   - It is well-typed, where the left hand-side is of type \\(\forall x : \alpha.\beta\\), the right hand side is of type \\(beta\\), and \\(e_{1}\ e_{2}\\) is of type \\(\beta\\).
-/
