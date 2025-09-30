import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Error

open Ast
open Dsl
open Ast.Expr

namespace Expr

-- M e : Syntax
def mk_m_type_eta (_ : Expr) : Expr :=
  ⟪ T Syntax ⟫

-- T (e : Syntax) : Type
def mk_t_type : Expr :=
  ⟪ (T Syntax) → Type ⟫

-- → : Type → Type → Syntax
def mk_arr_type : Expr :=
  ⟪ (T Type) → (T Type) → (T Syntax) ⟫

def mk_k_type : Expr :=
  ⟪ (T (M (S (K (-> Type))
      (S (K (S (K (-> Type))))
        (S (S (K S) (S (K K) ->))
              <-))))) ⟫

end Expr
