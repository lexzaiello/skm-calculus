import Mathlib.Data.Nat.Notation

inductive LExpr where
  -- ty, body
  | abstraction : LExpr → LExpr → LExpr
  | fall        : LExpr → LExpr → LExpr
  -- T and P, CoC
  | ty          : ℕ → LExpr
  | prp         : LExpr
  -- De Bruijn Index
  -- Start at 1
  | var         : ℕ      → LExpr
  | app         : LExpr  → LExpr → LExpr
deriving BEq

open LExpr

-- Variables bound to the lambda
def substitute (n_binders : ℕ) (with_expr : LExpr) : LExpr → LExpr
  | abstraction bind_ty body => abstraction (substitute n_binders.succ with_expr bind_ty) (substitute n_binders.succ with_expr body)
  | fall bind_ty body => fall (substitute n_binders.succ with_expr bind_ty) (substitute n_binders.succ with_expr body)
  | t@(ty _) => t
  | prp => prp
  | var n => if n_binders == n then with_expr else var (n - 1)
  | app lhs rhs =>
    app (substitute n_binders with_expr lhs) (substitute n_binders with_expr rhs)

def eval (e : LExpr) : Option LExpr :=
  match e with
    | app lhs rhs =>
      match eval lhs with
        | abstraction _ body => pure $ substitute 1 rhs body
        | _ => none
    | x => pure x

def infer (e : LExpr) : StateT (List LExpr) Option LExpr :=
  do match e with
    | prp => pure $ ty 0
    | ty n => pure $ ty $ n + 1
    | fall e_ty e_body  =>
      -- Set type and normal form of bound vars with idx
      -- to the inferred type of e_ty
      let e_ty' ← infer e_ty

      StateT.modifyGet (⟨(), e_ty' :: .⟩)

      -- Use new inference rules to infer body type
      -- This is the type of the entire expression
      infer e_body
    | abstraction e_ty e_body =>
      -- Pretty similar thing to forall
      let norm_e_ty ← infer e_ty
      StateT.modifyGet (⟨(), norm_e_ty :: .⟩)

      pure $ fall norm_e_ty (← infer e_body)
    | app lhs rhs =>
      match ← infer lhs with
        | (fall bind_ty body) =>
          let ty_rhs ← infer rhs

          if ty_rhs != bind_ty then
            -- These are technically also the same if they are beta
            -- normally equivalent
            let ty_rhsβ := eval ty_rhs
            let bind_tyβ := eval bind_ty

            if ty_rhsβ != bind_tyβ then
              none

          pure $ substitute 1 body rhs
        | _ => none
    | var idx =>
      let types ← StateT.get
      types[idx]?

def type_of (e : LExpr) : Option LExpr := Prod.fst <$> (infer e).run List.nil
