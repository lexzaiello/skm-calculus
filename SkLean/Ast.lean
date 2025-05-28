import Mathlib.Data.Nat.Notation

structure BindId where
  toNat : ℕ
deriving BEq

namespace BindId

def succ (id : BindId) : BindId := ⟨id.toNat.succ⟩

end BindId

inductive SkExpr where
  | k    : SkExpr
  | s    : SkExpr
  | prp  : SkExpr
  | ty   : ℕ      → SkExpr
  | fall : SkExpr → SkExpr → SkExpr
  | call : SkExpr → SkExpr → SkExpr
  | var  : BindId → SkExpr

namespace SkExpr

def substitute (in_expr : SkExpr) (n : BindId) (with_expr : SkExpr) : SkExpr :=
  match in_expr with
    | fall bind_ty body =>
      fall (bind_ty.substitute n.succ with_expr) (body.substitute n.succ with_expr)
    | var n' => if n == n' then with_expr else var $ ⟨n.toNat - 1⟩
    | x => x

def eval_once : SkExpr → SkExpr
  | call (call k x) _ => x
  | call (call (call s x) y) z => call (call x z) (call y z)
  | x => x

end SkExpr
