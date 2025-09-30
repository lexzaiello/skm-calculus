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
  | t    : Expr
  | app  : Expr → Expr → Expr
  | ty   : Expr
  | stx  : Expr
deriving BEq, Repr, Lean.ToExpr

end Ast
