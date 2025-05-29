import SkLean.Ast
import SkLean.Dsl
import SkLean.Sk

open SkExpr

#eval ty_k
#eval ty_k.substitute ⟨0⟩ ty_k
#eval ty_s
#eval (type_of_unsafe [] SK[K]) == ty_k
#eval (type_of_unsafe [] SK[K])
#eval (type_of_unsafe [] SK[(K ty_k)]) == SK[∀ β : Type 0, ∀ x : ty_k, ∀ y : #β, ty_k]
#eval (type_of_unsafe [] SK[((K ty_k) ty_k)]) == SK[∀ x : ty_k, ∀ y : ty_k, ty_k]

#eval (type_of_unsafe [] (let x := SK[((K ty_k) (∀ y : Type 0, ty_k))]
  let y := SK[((K ty_k) (Type 0))]
  let z := SK[K]
  let ty_x := SK[∀ x : ty_k, ∀ y : (∀ y : Type 0, ty_k), ty_k]
  let ty_y := SK[∀ x : ty_k, ∀ y : Type 0, ty_k]
  let ty_z := ty_k
  SK[((((((S ty_x) ty_y) ty_z) x) y) z)])) == ty_k
