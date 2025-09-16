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

namespace Expr

def toStringImpl : Expr → String
  | .k => "K"
  | .s => "S"
  | .m => "M"
  | .imp => "(→)"
  | .imp' => "(←)"
  | .t => "T"
  | .app (.app .imp t_in) t_out => s!"({toStringImpl t_in} → {toStringImpl t_out})"
  | .app lhs rhs => s!"({toStringImpl lhs} {toStringImpl rhs})"
  | .ty => "Type"
  | .stx => "Syntax"

instance : ToString Expr where
  toString := toStringImpl

end Expr

end Ast
