import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Error

open Ast
open Dsl

namespace Expr

-- Type : T Syntax
def mk_type_type : Expr :=
  ⟪ T Syntax ⟫

-- Syntax : T Syntax
def mk_type_syntax : Expr :=
  ⟪ T Syntax ⟫

def mk_m_k_type : Expr :=
  ⟪ (Type → Type → (T Syntax)) ⟫

def mk_m_s_type : Expr :=
   ⟪ (Type → Type → (T Syntax)) ⟫

def mk_t_type : Expr :=
  ⟪ ((T Syntax) → Type) ⟫

-- α → β : Syntax
def mk_arr_type : Expr :=
  ⟪ (Type → (Type → (T Syntax))) ⟫

def mk_k_type : Expr :=
  ⟪ M K ⟫

def mk_s_type : Expr :=
  ⟪ M S ⟫

end Expr
