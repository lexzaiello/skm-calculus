
# Table of Contents

1.  [Abstract](#org8bc1d86)
2.  [A Type Discipline for the SK Combinators](#org880b691)
3.  [Decomposition of the Simply-Typed Lambda Calculus into Dependently Typed SK Combinators](#orge05bde1)
    1.  [Type Expressivity & Equivalence](#org1c562a6)
4.  [Proof](#org693bffa)
    1.  [Comprehensiveness of the SK Mapping](#org94aaf17)
    2.  [Strong Normalization of the Typed SK Combinators](#org44940b6)
    3.  [Strong Normalization of the STLC](#org0b0ef6b)
    4.  [Encoding in Lean](#org33dd6f7)



<a id="org8bc1d86"></a>

# Abstract

Proofs of strong normalization of the simply-typed lambda calculus have been exhaustively enumerated in the literature. A common strategy invented by W. W. Tait known as "Tait's method," (Robert Harper, 2022) interprets types as sets of "well-behaving" terms which are known to be strongly normalizing and composed of expressions in some such set.
Strong normalization of the typed SK combinator calculus has been comparatively under-studied. Herein, I demonstrate that the typical proof of strong normalization using Tait's method holds for the typed SK combinator calculus. I also show that decomposition of the STLC into SK combinator expressions simplifies the typical proof of strong normalization.


<a id="org880b691"></a>

# A Type Discipline for the SK Combinators

I consider the usual SK combinator calculus defined as such:

A natural interpretation of the combinators as typed functions results in the dependent typing:

\label{inference:1}

\label{decomplemma:1}


<a id="orge05bde1"></a>

# Decomposition of the Simply-Typed Lambda Calculus into Dependently Typed SK Combinators

I utilize an SK compilation scheme outlined in "The Implementation of Functional Programming Languages" (Peyton Jones, Simon L., 1987):

I consider a generic simply-typed lambda calculus with base types $B$, a type constructor &rarr; and the type universe:

\label{maplemma:1}


<a id="org1c562a6"></a>

## Type Expressivity & Equivalence

I define a mapping (M<sub>t</sub>) from the &rarr; type constructor to &forall;: $(\alpha \rightarrow \beta) \mapsto \forall x : \alpha.\beta$. I also assume the existence of a mapping (M<sub>c</sub>) from the base types $B$ to arbitrary objects in my dependently-typed SK combinator calculus. Type inference is trivially derived from the above inference rules: $\forall c \in B, \exists\ t, t', c : t \implies t' = M_{t} t \implies M_{c} : t$.

It follows that every well-typed expression in our simply-typed lambda calculus has an equivalent well-typed SK expression:


<a id="org693bffa"></a>

# Proof

In order to prove strong normalization of the STLC, it suffices to demonstrate that a) no well-typed lambda calculus expression is inexpressible in the dependently-typed SK combinator calculus; and b) all well-typed SK combinator expressions are strongly normalizing.


<a id="org94aaf17"></a>

## Comprehensiveness of the SK Mapping


<a id="org44940b6"></a>

## Strong Normalization of the Typed SK Combinators


<a id="org0b0ef6b"></a>

## Strong Normalization of the STLC


<a id="org33dd6f7"></a>

## Encoding in Lean

Peyton Jones, Simon L. (1987). *The Implementation of Functional Programming Languages (Prentice-Hall International Series in Computer Science)*, Prentice-Hall, Inc..

Robert Harper (2022). *How to (Re)Invent Tait’s Method*.

