import SkLean.Ast3
import SkLean.Eval

inductive IsComb : Ast.Expr → Prop
  | k   : IsComb SKM[K]
  | s   : IsComb SKM[S]
  | m   : IsComb SKM[M]
  | arr : IsComb SKM[#~>]

inductive HasType : Ast.Expr → Ast.Expr → Prop
  | comb : IsComb e
    → HasType e SKM[(M e)]
  | k₁   : HasType α t_α
    → HasType SKM[(K α)] SKM[((M K) α)]
  | k    : HasType α t_α
    → HasType β t_β
    → HasType SKM[((K α) β)] SKM[(α ~> β ~> α)]
  | s₁   : HasType α t_α
    → HasType SKM[(S α)] SKM[((M S) α)]
  | s₂   : HasType α t_α
    → HasType β t_β
    → HasType SKM[((S α) β)] SKM[(((M S) α) β)]
  | s    : HasType α t_α
    → HasType β t_β
    → HasType γ t_γ
    → HasType SKM[(((S α) β) γ)] SKM[(α ~> β ~> γ ~> ((α γ) (β γ)))]
  | m_m  : IsComb e
    → HasType SKM[(M e)] SKM[Prp]
  | prp  : HasType SKM[Prp] SKM[Ty 0]
  | ty   : HasType SKM[Ty n] SKM[Ty n.succ]
  | arr  : HasType SKM[t_in ~> t_out] SKM[Ty 0]
  -- Non-dependent
  | call : HasType lhs SKM[t_in ~> t_out]
    → HasType rhs t_in
    → HasType SKM[(lhs rhs)] t_out

namespace HasType

theorem preservation (h : HasType e t) (h : Expr.eval_once e = .some e') : HasType e' t := by
  sorry

end HasType
