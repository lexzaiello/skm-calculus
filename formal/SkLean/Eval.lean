import SkLean.Ast3

namespace Expr

def insert_arrow_arg (in_e e : Ast.Expr) : Ast.Expr :=
  match in_e with
  | SKM[(t_in ~> t_out)] =>
    SKM[(t_in ~> #(insert_arrow_arg t_out e))]
  | x => SKM[(x e)]

def eval_once : Ast.Expr → Option Ast.Expr
  | SKM[(((((K _ _) _α) _β) x) _y)] => pure x
  | SKM[(((((((S _ _ _) _α) _β) _γ) x) y) z)] => pure SKM[((x z) (y z))]
  | SKM[(M (K m n))]     => pure $ Ast.Expr.mk_k_type m n
  | SKM[((((M (S _ _ _ )) α) β) γ)] => pure $ Ast.Expr.mk_s_type SKM[(M α)] α β γ
  | SKM[(M (lhs rhs))] => pure SKM[((M lhs) rhs)]
  | SKM[((_t_in ~> t_out) arg)]
  | SKM[((t_out <~ _t_in) arg)] => SKM[(t_out arg)]
  | SKM[(((M (<~)) t_out) _)]
  | SKM[(((M (~>)) _) t_out)] => SKM[(M t_out)]
  | SKM[(((M (→)) t_in) t_out)]
  | SKM[(((M (←)) t_out) t_in)]=>
    let max_u := max t_in.max_universe t_out.max_universe

    SKM[Ty max_u]
  | SKM[((_t_in → t_out) _)] => t_out
  | SKM[((t_out ← _t_in) _)] => t_out
  | SKM[(lhs rhs)] => do SKM[((#(← eval_once lhs)) rhs)]
  | _ => .none

def eval_n : ℕ → Ast.Expr → Option Ast.Expr
  | 0, _ => .none
  | n + 1, e => do
    let e' ← eval_once e
    eval_n n e'

partial def eval_unsafe (e : Ast.Expr) : Option Ast.Expr := do
  let e' ← eval_once e
  (eval_unsafe e').getD e'

end Expr

inductive IsEvalOnce : Ast.Expr → Ast.Expr → Prop
  | k      : IsEvalOnce SKM[(((((K _ _) _α) _β) x) y)]          x
  | s      : IsEvalOnce SKM[(((((((S _ _ _) _α) _β) _γ) x) y) z)] SKM[((x z) (y z))]
  | m_k    : IsEvalOnce SKM[(M (K _m n))]                        (Ast.Expr.mk_k_type _m n)
  | m_s    : IsEvalOnce SKM[((((M (S _ _ _)) α) β) γ)]            (Ast.Expr.mk_s_type SKM[(M α)] α β γ)
  | m_call : IsEvalOnce SKM[(M (lhs rhs))] SKM[((M lhs) rhs)]
  | pi     : IsEvalOnce SKM[((_t_in ~> t_out) arg)] SKM[(t_out arg)]
  | pi'    : IsEvalOnce SKM[((t_out <~ _t_in) arg)] SKM[(t_out arg)]
  | arr    : IsEvalOnce SKM[((_t_in → t_out) _)] t_out
  | arr'   : IsEvalOnce SKM[((t_out ← _t_in) _)] t_out
  | left   : IsEvalOnce lhs lhs'
    → IsEvalOnce SKM[(lhs rhs)] SKM[(lhs' rhs)]

abbrev BetaEq := Relation.ReflTransGen (λ x y => IsEvalOnce x y ∨ IsEvalOnce y x)

namespace BetaEq

lemma step : IsEvalOnce e e' → BetaEq e e' := (Relation.ReflTransGen.tail Relation.ReflTransGen.refl) ∘ Or.inl

lemma trans (h_beq₁ : BetaEq a₁ a₂) (h_beq₂ : BetaEq a₂ a₃) : BetaEq a₁ a₃ := Relation.ReflTransGen.trans h_beq₁ h_beq₂

lemma symm (h : BetaEq a₁ a₂) : BetaEq a₂ a₁ := by
  apply Relation.ReflTransGen.symmetric
  intro x y h
  cases h
  repeat simp_all

end BetaEq


