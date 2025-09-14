import Mathlib.Tactic
import Lean
import Lean.Elab.Term

namespace Ast

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | imp  : Expr
  | imp' : Expr
  | app  : Expr → Expr → Expr
  | ty   : Expr
deriving BEq, Repr, Lean.ToExpr

end Ast
