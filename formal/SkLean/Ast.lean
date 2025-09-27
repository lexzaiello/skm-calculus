import Mathlib.Tactic
import Lean
import Lean.Elab.Term

namespace Ast

inductive Expr where
  | s       : Expr
  | k       : Expr
  | ty      : Expr
  | app     : Expr → Expr → Expr
deriving BEq, Repr, Lean.ToExpr

namespace Expr

def toStringImpl : Expr → String
  | .s => "S"
  | .k => "K"
  

instance : ToString Expr where
  toString := toStringImpl

end Expr

end Ast
