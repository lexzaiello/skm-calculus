import SkLean.Ast3

namespace Expr

def eval_once : Ast.Expr → Option Ast.Expr
  | SKM[((((K _α) _β) x) _y)] => pure x
  | SKM[((((((S _α) _β) _γ) x) y) z)] => pure SKM[((x z) (y z))]
  | SKM[(((M K) α) β)]     => pure SKM[(α ~> (β ~> α))]
  | SKM[((((M S) α) β) γ)] => pure SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | SKM[(M (lhs rhs))] => pure SKM[((M lhs) rhs)]
  | SKM[((_t_in ~> t_out) _arg)] => t_out
  | _ => .none

end Expr
