# Existing Work: Typed SK Combinators

## Definition of the SK Combinators

1. Schonfinkel, M. - [[https://content.wolfram.com/sites/43/2020/12/Schonfinkel-OnTheBuildingBlocksOfMathematicalLogic.pdf][On the building blocks of mathematical logic]]
- Schonfinkel defines \(C\) and \(S\) combinators:

$$
S x y z = x z (y z)
C x y = x
$$

- Schonfinkel demonstrates that the \(I\) combinator (\(I x = x\)) can be constructed using only \\(K\\) (or by the name \\(C\\)) and \\(S\\). 
- Schonfinkel demonstrates that every logical formula can be expressed using the combinators \\(S\\) and \\(K\\).

## Strong Normalization of the SK Combinators



## Common Dependent Typings of the Combinators

1. Altenkirch, T. - [[https://types2023.webs.upv.es/TYPES2023.pdf#page=194][Towards dependent combinator calculus]]

- A dependent typing of the \\(S\\) and \\(K\\) is given:

$$
K : \{A : Set\} {B : A \rightarrow Set} \rightarrow (a : A) \rightarrow B\ a \rightarrow A
$$



