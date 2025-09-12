import Mathlib.Tactic
import Lean
import Lean.Elab.Term

namespace Ast

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | pi   : Expr
  | pi'  : Expr
  | imp  : Expr
  | imp' : Expr
  | hole : Expr
  | app : Expr → Expr → Expr
deriving BEq, Repr, Lean.ToExpr

end Ast
