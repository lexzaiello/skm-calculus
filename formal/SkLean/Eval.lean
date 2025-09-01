import SkLean.Ast3

namespace Expr

def eval_once : Ast.Expr → Option Ast.Expr
  | SKM[((((K _α) _β) x) _y)] => pure x
  | SKM[((((((S _α) _β) _γ) x) y) z)] => pure SKM[((x z) (y z))]
  | SKM[(((M K) α) β)]     => pure SKM[(α ~> (β ~> α))]
  | SKM[((((M S) α) β) γ)] => do
    let lhs' := (eval_once SKM[(α γ)]).getD SKM[(α γ)]
    let rhs' := (eval_once SKM[(β γ)]).getD SKM[(β γ)]

    pure SKM[(lhs' rhs')]
  | SKM[(M (lhs rhs))] => pure SKM[((M lhs) rhs)]
  | SKM[(M Ty n)] => SKM[Ty n.succ]
  | SKM[(M Prp)] => SKM[Ty 0]
  | SKM[(((M #~>) _t_in) _t_out)] => SKM[Ty 0]
  | SKM[((_t_in ~> t_out) _arg)] => t_out
  | SKM[(lhs rhs)] => do SKM[((#(← eval_once lhs)) rhs)]
  | _ => .none

end Expr
