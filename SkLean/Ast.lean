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
  | call : SkExpr → SkExpr → SkExpr
  | prp  : SkExpr

namespace SkExpr

def eval_once : SkExpr → SkExpr
  | call (call k x) _ => x
  | call (call (call s x) y) z => call (call x z) (call y z)
  | x => x

end SkExpr

inductive SkType where
  | ty   : ℕ      → SkType
  | fall : SkType → SkType → SkType
  | var  : BindId → SkType

namespace SkType

def substitute (in_expr : SkType) (n : BindId) (with_expr : SkType) : SkType :=
  match in_expr with
    | fall bind_ty body =>
      fall (bind_ty.substitute n.succ with_expr) (body.substitute n.succ with_expr)
    | var n' => if n == n' then with_expr else var $ ⟨n.toNat - 1⟩
    | ty n => ty n

end SkType
