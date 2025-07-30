import Mathlib.Tactic
import SkLean.Ast3

partial def eval (e : Expr) : Expr :=
  let e' := match e with
    | SKM[((K x) _y)] => x
    | SKM[(((S x) y) z)] => SKM[((x z) (y z))]
    | SKM[(M (lhs rhs))] => SKM[((M lhs) rhs)]
    | SKM[(M K)] => SKM[((S (K M)) K)]
    | SKM[(M S)] => SKM[((S (K M)) S)]
    | SKM[(lhs rhs)] => SKM[((#(eval lhs)) rhs)]
    | x => x

  if e' == e then
    e
  else
    eval e'

def eval_n (n : ℕ) (e : Expr) : Expr :=
  if n = 0 then
    e
  else
    match e with
      | SKM[((K x) _y)] => x
      | SKM[(((S x) y) z)] => eval_n n.pred SKM[((x z) (y z))]
      | SKM[(M (lhs rhs))] => eval_n n.pred SKM[((M lhs) rhs)]
      | SKM[(M K)] => SKM[((S (K M)) K)]
      | SKM[(M S)] => SKM[((S (K M)) S)]
      | SKM[(lhs rhs)] => eval_n n.pred.pred SKM[((#(eval_n n.pred lhs)) rhs)]
      | x => x

partial def type_of (e : Expr) : Expr :=
  match e with
    | SKM[S] => SKM[((S (K M)) S)]
    | SKM[M] => SKM[(M M)]
    | SKM[K] => SKM[((S (K M)) K)]
    | SKM[(lhs rhs)] => eval SKM[(M (lhs rhs))]

def type_of_safe (gas : ℕ) (e : Expr) : Expr :=
  match e with
    | SKM[S] => SKM[((S (K M)) S)]
    | SKM[M] => SKM[((S (K M)) M)]
    | SKM[K] => SKM[((S (K M)) K)]
    | SKM[(lhs rhs)] => eval_n gas.pred SKM[(M (lhs rhs))]

#eval eval SKM[((K S) K)]
#eval type_of_safe 202 SKM[((K S) K)]

#eval eval_n 20 SKM[(M ((K K) K))]
#eval eval_n 14 SKM[(M (M M))]
#eval type_of_safe 16 SKM[(((S K) K) K)] |> eval_n 13

-- Pair
#eval eval SKM[(((S ((S K) K)) (K K)) ((((S (K ((S (K S)) K))) K) K) S))]
