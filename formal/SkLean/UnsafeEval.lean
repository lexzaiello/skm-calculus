import SkLean.Ast3

namespace Expr

partial def eval_unsafe (e : Ast.Expr) : Ast.Expr :=
  match e with
  | SKM[((((K _α) _β) x) _y)] => eval_unsafe x
  | SKM[((((((S _α) _β) _γ) x) y) z)] => eval_unsafe SKM[((x z) (y z))]
  | SKM[(((M K) α) β)] => SKM[(α ~> (β ~> α))]
  | SKM[((((M S) α) β) γ)] => SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | SKM[(M (Ty n))] => SKM[(Ty n.succ)]
  | SKM[((_α ~> β) _rhs)] => eval_unsafe β
  | x => x

end Expr
