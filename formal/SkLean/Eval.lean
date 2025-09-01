import SkLean.Ast3

namespace Expr

def eval_once : Ast.Expr → Option Ast.Expr
  | SKM[((((K _α) _β) x) _y)] => pure x
  | SKM[((((((S _α) _β) _γ) x) y) z)] => pure SKM[((x z) (y z))]
  | SKM[(((M K) α) β)]     => pure SKM[(α ~> (((K (Ty 0)) α) (β ~> (((K (M β)) α) β))))]
  | SKM[((((M S) α) β) γ)] => pure SKM[(α ~> ((((K (Ty 0))) α) (β ~> ((((K (Ty 0)) β) (γ ~> (((((S (M α)) (M β)) γ) α) β)))))))]
  | SKM[((M M) K)] => pure SKM[Prp]
  | SKM[((M M) S)] => pure SKM[Prp]
  | SKM[((M M) M)] => pure SKM[Prp]
  | SKM[((M M) #~>)] => pure SKM[Prp]
  | SKM[(M (lhs rhs))] => pure SKM[((M lhs) rhs)]
  | SKM[(M Ty n)] => SKM[Ty n.succ]
  | SKM[(M Prp)] => SKM[Ty 0]
  | SKM[(((M #~>) _t_in) _t_out)] => SKM[Ty 0]
  | SKM[((_t_in ~> t_out) arg)] => SKM[(t_out arg)]
  | SKM[(lhs rhs)] => do SKM[((#(← eval_once lhs)) rhs)]
  | _ => .none

def eval_n : ℕ → Ast.Expr → Option Ast.Expr
  | 0, _ => .none
  | n + 1, e => do
    let e' ← eval_once e
    eval_n n e'

end Expr

inductive IsEvalOnce : Ast.Expr → Ast.Expr → Prop
  | k      : IsEvalOnce SKM[((((K _α) _β) x) y)]          x
  | s      : IsEvalOnce SKM[((((((S _α) _β) _γ) x) y) z)] SKM[((x z) (y z))]
  | m_k    : IsEvalOnce SKM[(((M K) α) β)]                SKM[(α ~> (((K (Ty 0)) α) (β ~> (((K (M β)) α) β))))]
  | m_s    : IsEvalOnce SKM[((((M S) α) β) γ)]            SKM[(α ~> ((((K (Ty 0))) α) (β ~> ((((K (Ty 0)) β) (γ ~> (((((S (M α)) (M β)) γ) α) β)))))))]
  | m_m_k  : IsEvalOnce SKM[((M M) K)] SKM[Prp]
  | m_m_s  : IsEvalOnce SKM[((M M) S)] SKM[Prp]
  | m_m_m  : IsEvalOnce SKM[((M M) M)] SKM[Prp]
  | m_m_a  : IsEvalOnce SKM[((M M) #~>)] SKM[Prp]
  | m_call : IsEvalOnce SKM[(M (lhs rhs))] SKM[((M lhs) rhs)]
  | m_ty   : IsEvalOnce SKM[(M Ty n)] SKM[Ty n.succ]
  | m_prp  : IsEvalOnce SKM[(M Prp)] SKM[Ty 0]
  | m_arr  : IsEvalOnce SKM[(((M #~>) _t_in) _t_out)] SKM[Ty 0]
  | arr    : IsEvalOnce SKM[((_t_in ~> t_out) arg)] SKM[(t_out arg)]
  | left   : IsEvalOnce lhs lhs'
    → IsEvalOnce SKM[(lhs rhs)] SKM[(lhs' rhs)]

def BetaEq := Relation.ReflTransGen (λ x y => IsEvalOnce x y ∨ IsEvalOnce y x)
