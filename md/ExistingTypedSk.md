# Existing Work: Typed SK Combinators

## Definition of the SK Combinators

1. Schonfinkel, M. - [On the building blocks of mathematical logic](https://content.wolfram.com/sites/43/2020/12/Schonfinkel-OnTheBuildingBlocksOfMathematicalLogic.pdf)
   - Schonfinkel defines \\(C\\) and \\(S\\) combinators:

   $$
   S x y z = x z (y z) \\\\
   C x y = x
   $$

   - Schonfinkel demonstrates that the \\(I\\) combinator (\\(I x = x\\)) can be constructed using only \\(K\\) (or by the name \\(C\\)) and \\(S\\). 
   - Schonfinkel demonstrates that every logical formula can be expressed using the combinators \\(S\\) and \\(C\\) (also known as \\(K\\)).

## Strong Normalization of the SK Combinators

1. Abel, A. - Strong normalization for simply-typed combinatory algebra using Girard’s reducibility candidates formalized in Agda](https://www.cse.chalmers.se/~abela/agda/cr-sk.pdf).
   - A formal proof of strong normalization of the simply-typed SK combinators is provided in Agda.
   - The proof utilizes Girard's reducibility candidates.

## Common Typings of the Combinators

### Simple Typing

1. Tarau, P. - [On Synergies between Type Inference, Generation and Normalization of SK-combinator Trees](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=7426077)
   - The standard definitions of \\(S\\) and \\(K\\) are utilized.
   - A simple-typing of the \\(SK\\) combinators is formalized in Prolog.

### Dependent Typing

1. Altenkirch, T. - [Towards dependent combinator calculus](https://types2023.webs.upv.es/TYPES2023.pdf#page=194)
   - A dependent typing of \\(S\\) and \\(K\\) is given with type universes:

   $$
   U : Set \\\\
   EI : U \rightarrow Set \\\\
   u : U \\\\
   K : \\{A : U\\}\ \\{B : EI\ A \rightarrow U\\} \rightarrow (a : EI\ A) \rightarrow EI\ (B\ a) \rightarrow EI\ A \\\\
   S : \\{A : U\\}\ \\{B : EI\ A \rightarrow U\\}\ \\{C : (a : EI\ A) \rightarrow EI\ (B\ a) \rightarrow U\\} \\\\
     \rightarrow ((a : EI\ A)) (b : B EI\ (B\ a)) \rightarrow EI\ (C\ a\ b)) \\\\
	 \rightarrow (g : (a : EI\ A) \rightarrow EI\ (B\ a)) \\\\
	 \rightarrow (a : EI\ A) \rightarrow EI\ (C\ a\ (g\ a))
   $$

   - No formal proof of strong normalization is provided.

## Gap

As of yet, it remains to be explored whether the dependent \\(SK\\) combinators are provably strongly normalizing.
Furthermore, mechanizing such a proof in a language like Lean is of particular interest.
In this paper, I do so, building off existing dependent typings of the SK combinators, and Girard's reducibility candidates.
