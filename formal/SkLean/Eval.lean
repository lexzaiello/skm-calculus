import SkLean.Ast3

namespace Expr

def eval_once : Ast.Expr → Option Ast.Expr
  | SKM[((((K _α) _β) x) _y)] => pure x
  | SKM[((((((S _α) _β) _γ) x) y) z)] => pure SKM[((x z) (y z))]
  | SKM[(((M K) α) β)]     => pure SKM[(α ~> (β ~> (((K (M β)) α) β)))]
  | SKM[((((M S) α) β) γ)] => pure SKM[(α ~> β ~> γ ~> (((((S (M α)) (M β)) γ) α) β))]
  | SKM[((M M) K)] => pure SKM[Prp]
  | SKM[((M M) S)] => pure SKM[Prp]
  | SKM[((M M) M)] => pure SKM[Prp]
  | SKM[((M M) #~>)] => pure SKM[Prp]
  | SKM[(M (lhs rhs))] => pure SKM[((M lhs) rhs)]
  | SKM[(M Ty n)] => SKM[Ty n.succ]
  | SKM[(M Prp)] => SKM[Ty 0]
  | SKM[(((M #~>) _t_in) _t_out)] => SKM[Ty 0]
  | SKM[((_t_in ~> t_out) _arg)] => t_out
  | SKM[(lhs rhs)] => do SKM[((#(← eval_once lhs)) rhs)]
  | _ => .none

def eval_n : ℕ → Ast.Expr → Option Ast.Expr
  | 0, _ => .none
  | n + 1, e => do
    let e' ← eval_once e
    eval_n n e'

end Expr

inductive IsEvalOnce : Ast.Expr → Ast.Expr → Prop
  | k   : IsEvalOnce SKM[((((K _α) _β) x) y)] x
  | s   : IsEvalOnce SKM[((((((S _α) _β) _γ) x) y) z)] SKM[((x z) (y z))]
  | m_k : IsEvalOnce SKM[(((M K) α) β)] SKM[(α ~> β ~> α)]
  | m_s : IsEvalOnce SKM[((((M S) α) β) γ)] SKM[(α ~> β ~> γ ~> ((α γ) (β γ)))]

def BetaEq := Relation.ReflTransGen (λ x y => Expr.eval_once x = .some y ∨ Expr.eval_once y = .some x)
