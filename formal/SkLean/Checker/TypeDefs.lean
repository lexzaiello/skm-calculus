import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Error

open Ast
open Dsl
open Ast.Expr

namespace Expr

def mk_k_type_eta (α β : Expr) : Expr :=
  ⟪ M ((#α) → ((#β) → (#α))) ⟫

#eval mk_k_type_eta ⟪ M ⟫ ⟪ M ⟫

end Expr
