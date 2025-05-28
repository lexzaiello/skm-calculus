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

inductive SkType where
  | ty   : ℕ      → SkType
  | fall : SkType → SkType → SkType
  | var  : BindId → SkType

