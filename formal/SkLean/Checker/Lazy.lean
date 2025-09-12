import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Error

open Ast
open Ast.Expr

namespace Expr

def infer_lazy : Expr → Except (@TypeError Ast.Expr) Ast.Expr
  | 

end Expr

