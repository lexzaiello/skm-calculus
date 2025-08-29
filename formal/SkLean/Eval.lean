import SkLean.Ast3

namespace Expr

def eval_once : Ast.Expr → Option Ast.Expr
  | SKM[((((K _α) _β) x) _y)] => pure x
  | SKM[((((((S _α) _β) _γ) x) y) z)] => pure SKM[((x z) (y z))]
  | SKM[(((M K) α) β)]     => pure SKM[(α ~> (β ~> α))]
  | SKM[((((M S) α) β) γ)] => pure SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | SKM[(M (Ty n))] => pure SKM[Ty n.succ]
  | SKM[((M t_in) ~> t_out)] => pure SKM[(t_in ~> (M t_out))]
  | SKM[(M (lhs rhs))] => pure SKM[((M lhs) rhs)]
  | SKM[((_t_in ~> t_out) _arg)] => t_out
  | x => x

end Expr
