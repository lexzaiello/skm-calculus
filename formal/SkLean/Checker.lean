import SkLean.Ast3
import SkLean.Eval

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
  | SKM[K]
  | SKM[M]
  | SKM[S]
  | SKM[(K _α)]
  | SKM[(S _α)]
  | SKM[((S _α) _β)]
  | SKM[#~>]
  | SKM[(#~> _t_in)] => true
  | SKM[(m_e e)] => all_m m_e ∧ is_typed_comb e
  | _ => false

def add_m : Ast.Expr → Ast.Expr
  | SKM[M]    => SKM[(M M)]
  | SKM[_]    => SKM[(M _)]
  | SKM[K]    => SKM[(M K)]
  | SKM[S]    => SKM[(M S)]
  | SKM[#~>]  => SKM[(M #~>)]
  | SKM[(lhs rhs)] => SKM[((#(add_m lhs)) rhs)]

partial def infer_unsafe : Ast.Expr → Except (@TypeError Ast.Expr) Ast.Expr
  | SKM[K]               => pure SKM[(M K)]
  | SKM[S]               => pure SKM[(M S)]
  | SKM[M]               => pure SKM[(M M)]
  | SKM[#~>]             => pure SKM[(M #~>)]
  | SKM[(M K)]           => pure SKM[((M M) K)]
  | SKM[(M S)]           => pure SKM[((M M) S)]
  | SKM[(M M)]           => pure SKM[((M M) M)]
  | SKM[(M #~>)]         => pure SKM[((M M) #~>)]
  | SKM[_]               => .error $ .no_type_not_comb SKM[_]
  | SKM[((K α) β)]       => pure SKM[α !~> β !~> α]
  | SKM[(((K _) β) x)]   => do
    let α ← infer_unsafe x
    pure SKM[α !~> β !~> α]
  | SKM[(((S α) β) γ)]   => do
    let t_α ← infer_unsafe α
    pure $ Ast.Expr.mk_s_type t_α α β γ
  | SKM[(((((S α) _) γ) _x) y)]   => do
    let β ← infer_unsafe y
    let t_α ← infer_unsafe α
    pure $ Ast.Expr.mk_s_type t_α α β γ
  | SKM[(M e)] => do pure SKM[(M #(← infer_unsafe e))]
  | SKM[(t_in ~> t_out)] => pure SKM[(((M #~>) t_in) t_out)]
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

#eval Expr.infer_unsafe SKM[((((K (M K)) (M K)) K) K)]

#eval Expr.infer_unsafe SKM[((((((S ((M M) !~> ((M M) !~> (M M)) !~> (M M))) ((M M) !~> (M M) !~> (M M))) (M M)) ((K (M M)) ((M M) !~> (M M)))) ((K (M M)) (M M))) M)]

