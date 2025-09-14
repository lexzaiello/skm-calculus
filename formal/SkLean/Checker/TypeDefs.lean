import SkLean.Ast
import SkLean.Dsl.Core
import SkLean.Error

open Ast
open Dsl
open Ast.Expr

namespace Expr

def mk_arr_type : Expr :=
  ⟪ M (Type → Type → (M Type)) ⟫

def mk_k_type_eta (α β : Expr) : Expr :=
  ⟪ (#α) → (#β) → (#α) ⟫

def mk_k_type : Expr :=
  ⟪ S Type Type (Type → (M Type))
    (K (Type → (M Type)) Type
      (-> Type))
    (S Type ((Type → Type) → Type) (M Type)
      (K ((Type → Type) → Type → (M Type)) Type
        (S Type Type (M Type)
          (K (Type → (M Type)) Type
            (-> Type))))
      (S Type (Type → (M Type)) (M Type)
        (S Type (Type → Type → (M Type)) ((Type → (M Type)) → Type → (M Type))
          (K ((Type → Type → (M Type))) (M (Type → (M Type)))
            (S Type (M Type) (M Type)))
          (S Type (M (Type → (Type → (M Type)))) (M (Type → (M Type)))
            (K (M (Type → Type → (M Type))) Type
              (K (M (Type → (M Type))) Type)
              ->)
            <-)))) ⟫

#eval mk_k_type_eta ⟪ M ⟫ ⟪ M ⟫

end Expr
