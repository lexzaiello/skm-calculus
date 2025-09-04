import SkLean.Ast3
import SkLean.Eval
import SkLean.SType

inductive TypeError {α : Type} where
  | argument_mismatch (expected actual in_e arg : α) : TypeError
  | no_type_not_comb  (at_e : α)                     : TypeError
  | bad_type_not_comb (at_e in_e t : α)                   : TypeError

instance (α : Type) [ToString α] : ToString (@TypeError α) where
  toString
  | .argument_mismatch expected actual in_e arg => s!"Argument type mismatch in function application of {toString in_e} with {toString arg}. Expected {toString expected}, but found {toString actual}"
  | .no_type_not_comb at_e => s!"Type inference failed for {toString at_e}, but not a combinator."
  | .bad_type_not_comb at_e in_e t => s!"Type inference failed for {toString at_e} in app {toString in_e}. Expected an arrow, but got {toString t}, but not a combinator."

namespace Expr

def all_m : Ast.Expr → Bool
  | SKM[M] => true
  | SKM[(lhs rhs)] => all_m lhs ∧ all_m rhs
  | _ => false

def is_typed_comb : Ast.Expr → Bool
  | SKM[K _ _]
  | SKM[M]
  | SKM[S _ _ _]
  | SKM[(K _ _ _α)]
  | SKM[(S _ _ _ _α)]
  | SKM[((S _ _ _ _α) _β)]
  | SKM[~>]
  | SKM[(~> _t_in)] => true
  | SKM[(m_e e)] => all_m m_e ∧ is_typed_comb e
  | _ => false

def add_m : Ast.Expr → Ast.Expr
  | SKM[(lhs rhs)] => SKM[((#(add_m lhs)) rhs)]
  | e => SKM[(M e)]

partial def infer_unsafe : Ast.Expr → Except (@TypeError Ast.Expr) Ast.Expr
  | SKM[K _m n]          => pure $ Ast.Expr.mk_k_type _m n
  | SKM[S _m n o]        => pure SKM[_]
  | SKM[M]               => pure SKM[(M M)]
  | SKM[~>]              => pure SKM[(M (~>))]
  | SKM[<~]              => pure SKM[(M (<~))]
  | SKM[→]              => pure SKM[(M (→))]
  | SKM[←]              => pure SKM[(M (←))]
  | SKM[_]               => .error $ .no_type_not_comb SKM[_]
  | SKM[((K _ _ α) β)]       => pure SKM[α → β → α]
  | SKM[(((K _ _ _) β) x)]   => do
    let α ← infer_unsafe x
    pure SKM[α → β → α]
  | SKM[((((S _m n o) α) β) γ)]   => do
    let t_α ← infer_unsafe α
    pure $ Ast.Expr.mk_s_type t_α α β γ
  | SKM[((((((S _ _ _) α) _) γ) _x) y)]   => do
    let β ← infer_unsafe y
    let t_α ← infer_unsafe α
    pure $ Ast.Expr.mk_s_type t_α α β γ
  | SKM[(M e)] => do pure SKM[(M #(← infer_unsafe e))]
  | SKM[(t_in ~> t_out)] => infer_unsafe t_out
  | SKM[Prp] => pure SKM[Ty 0]
  | SKM[Ty n] => pure SKM[Ty n.succ]
  | SKM[(lhs rhs)]       => do
    let t_lhs ← infer_unsafe lhs
    let t_lhs' := (eval_unsafe t_lhs).getD t_lhs

    match t_lhs' with
    | SKM[(t_in ~> _t_out)] =>
      let found ← infer_unsafe rhs

      if found == t_in then
        pure $ (eval_unsafe SKM[(t_lhs' rhs)]).getD SKM[(t_lhs rhs)]
      else
        .error $ .argument_mismatch t_in t_lhs lhs rhs
    | e =>
      if is_typed_comb e then
        let with_m := SKM[((#(add_m lhs)) rhs)]
        pure $ (eval_unsafe with_m).getD with_m
      else
        .error $ .bad_type_not_comb lhs SKM[(lhs rhs)] t_lhs'

lemma valid_lhs (_h_t : infer_unsafe SKM[(lhs rhs)] = .ok t) : ∃ t_lhs, infer_unsafe lhs = t_lhs := by
  cases SKM[(lhs rhs)]
  repeat simp_all

lemma valid_rhs (_h_t : infer_unsafe SKM[(lhs rhs)] = .ok t) : ∃ t_rhs, infer_unsafe rhs = t_rhs := by
  cases SKM[(lhs rhs)]
  repeat simp_all

end Expr




