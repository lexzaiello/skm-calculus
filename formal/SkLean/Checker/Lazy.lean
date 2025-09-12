import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Error

open Ast
open Expr

namespace Ast

namespace Expr

def infer_lazy : Expr → Except (@TypeError Expr) Expr
  | ⟪ @S _m n o α β γ ⟫ => pure ⟪ (→) (#α) ((→) (#β) → (#α)) ⟫
  | ⟪ @K _m _n α β ⟫ => pure ⟪ (→) (#α) ((→) (#β) → (#α)) ⟫
  | e => pure ⟪ M #e ⟫

end Expr

end Ast
