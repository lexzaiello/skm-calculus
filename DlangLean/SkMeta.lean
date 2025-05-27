import DlangLean.CoC
import Mathlib.Tactic

-- K is dependently typed from
-- α : Type → β : Type → α → β
def K : TypeContext × LExpr :=
  let inner_return := abstraction 
