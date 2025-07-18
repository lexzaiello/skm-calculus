/-
# Explicit, Dependent Typing of \\(K\\)

Using our definition of the \\(\rightarrow\\) expression, we can define a coherent typing of \\(K\\) that comports with our desired judgment rules.

To recap, I aim for \\(\rightarrow\\) aims to serve as a genralized representation of a function type. Recall that \\(\rightarrow\ A\ B\\) is defined as such:

$$
\\(\rightarrow\ A\ B\\) = K (M B) A B
$$

For all arguments, \\(x : A\\), this expression produces the type \\(B\\). While \\(\rightarrow\\) might seem nondependent, since it encodes types of the form \\(A \rightarrow B\\), it can be **computed** and is derived from **computable** elements of the syntax tree. For example, we can provide \\(\rightarrow\\) as an argument to \\(S\\). 
-/
