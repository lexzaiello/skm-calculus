import SkLean.Ast3
import SkLean.Eval

inductive TypeError {α : Type} where
  | argument_mismatch (expected actual in_e arg : α) : TypeError
  | no_type_not_comb  (at_e : α)                 : TypeError

instance (α : Type) [ToString α] : ToString (@TypeError α) where
  toString
  | .argument_mismatch expected actual in_e arg => s!"Argument type mismatch in function application of {in_e} with {arg}. Expected {expected}, but found {actual}"
  | .no_type_not_comb at_e => s!"type inference failed for {at_e}, but not a combinator"

namespace Expr

def is_typed_comb : Ast.Expr → Bool
  | SKM[K]
  | SKM[M]
  | SKM[S]
  | SKM[(K _α)]
  | SKM[(S _α)]
  | SKM[((S _α) _β)]
  | SKM[#~>]
  | SKM[(#~> _t_in)] => true
  | SKM[(M e)] => is_typed_comb e
  | _ => false

def add_m : Ast.Expr → Ast.Expr
  | SKM[M]    => SKM[(M M)]
  | SKM[K]    => SKM[(M K)]
  | SKM[S]    => SKM[(M S)]
  | SKM[#~>]  => SKM[(M #~>)]
  | SKM[Ty n] => SKM[(M Ty n)]
  | SKM[Prp]  => SKM[(M Prp)]
  | SKM[(lhs rhs)] => SKM[((#(add_m lhs)) rhs)]

def infer : Ast.Expr → Except (@TypeError Ast.Expr) Ast.Expr
  | SKM[K]               => pure SKM[(M K)]
  | SKM[S]               => pure SKM[(M S)]
  | SKM[M]               => pure SKM[(M M)]
  | SKM[#~>]             => pure SKM[(M #~>)]
  | SKM[(M K)]           => pure SKM[Prp]
  | SKM[(M S)]           => pure SKM[Prp]
  | SKM[(M M)]           => pure SKM[Prp]
  | SKM[(M #~>)]         => pure SKM[Prp]
  | SKM[Prp]             => pure SKM[Ty 0]
  | SKM[Ty n]            => pure SKM[Ty n.succ]
  | SKM[((K α) β)]       => pure SKM[(α ~> (((K (Ty 0)) α) (β ~> (((K (M β)) α) β))))]
  | SKM[(((S α) β) γ)]   => pure SKM[(α ~> ((((K (Ty 0))) α) (β ~> ((((K (Ty 0)) β) (γ ~> (((((S (M α)) (M β)) γ) α) β)))))))]
  | SKM[(M e)] => do pure SKM[(M #(← infer e))]
  | SKM[(_t_in ~> _t_out)] => pure SKM[Ty 0]
  | SKM[(lhs rhs)]       => do
    let t_lhs ← infer lhs
    match t_lhs with
    | SKM[(t_in ~> t_out)] =>
      let found ← infer rhs

      if found == t_in then
        pure $ (eval_once SKM[(t_out rhs)]).getD SKM[(t_out rhs)]
      else
        .error $ .argument_mismatch t_in t_lhs lhs rhs
    | e =>
      if is_typed_comb e then
        let with_m := SKM[((#(add_m lhs)) rhs)]
        pure $ (eval_once with_m).getD with_m
      else
        .error $ .no_type_not_comb lhs

lemma valid_lhs (_h_t : infer SKM[(lhs rhs)] = .ok t) : ∃ t_lhs, infer lhs = t_lhs := by
  cases SKM[(lhs rhs)]
  repeat simp_all

lemma valid_rhs (_h_t : infer SKM[(lhs rhs)] = .ok t) : ∃ t_rhs, infer rhs = t_rhs := by
  cases SKM[(lhs rhs)]
  repeat simp_all

end Expr

example : Expr.infer SKM[((((K (M K)) (M K)) K) K)] = .ok SKM[(M K)] := rfl

