import Mathlib.Tactic
import Lean
import Lean.Elab.Term

namespace Ast

abbrev Universe := ℕ

inductive Expr where
  | k    : Universe → Universe → Expr
  | s    : Universe → Universe → Universe → Expr
  | m    : Expr
  | pi   : Expr
  | pi'  : Expr
  | imp  : Expr
  | imp' : Expr
  | ty   : Universe → Expr
  | prp  : Expr
  | hole : Expr
  | app : Expr → Expr → Expr
deriving BEq, Repr, Lean.ToExpr

namespace Expr

def max_universe : Expr → Universe
  | .k _m n => max _m n
  | .s _m n o => max (max _m n) o
  | .ty n => n
  | .app lhs rhs => max lhs.max_universe rhs.max_universe
  | _ => 0

end Expr

inductive ExprBox (e : Ast.Expr) where
  | mk : ExprBox e

namespace Expr

end Expr

def mk_k_type (_m n : Universe) : Ast.Expr :=
  sorry

end Ast
