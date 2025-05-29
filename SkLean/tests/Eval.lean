import SkLean.Ast
import SkLean.Sk
import SkLean.Dsl

open SkExpr

-- SKKK = K K (K K) = K
example :
  let x := SK[((K ty_k) (∀ y : Type 0, ty_k))]
  let y := SK[((K ty_k) (Type 0))]
  let z := SK[K]
  let ty_x := SK[∀ x : ty_k, ∀ y : (∀ y : Type 0, ty_k), ty_k]
  let ty_y := SK[∀ x : ty_k, ∀ y : Type 0, ty_k]
  let ty_z := ty_k
  beta_eq SK[((((((S ty_x) ty_y) ty_z) x) y) z)] SK[K] := by
  repeat unfold NamedSkExpr.to_sk_expr at *
  simp_all
  apply beta_eq.symm
  apply beta_eq.hard
  unfold eval_once
  simp
  apply beta_eq.hard
  unfold eval_once
  simp
  exact beta_eq.trivial k k rfl

example : eval_once SK[((((K k_ty) k_ty) K) K)]  = k := by
  unfold eval_once
  repeat unfold NamedSkExpr.to_sk_expr
  simp
