import Mathlib.Tactic

inductive LExpr where
  -- Bind var de brujin index, ty, body
  | abstraction : ℕ → LExpr → LExpr → LExpr
  | fall        : ℕ → LExpr → LExpr → LExpr
  -- T and P, CoC
  | ty          : ℕ → LExpr
  | prp         : LExpr
  -- Bound variable
  | bvar        : ℕ      → LExpr
  | app         : LExpr  → LExpr → LExpr
deriving BEq

open LExpr

-- inference rules:
-- 1. prop is of type type
-- 2. if A is of type K, and x is of type A, then x is of type A
  -- This seems trivial?
-- 3. if A is of type K, and x is of type A, and B has type L
-- then (∀x:A.B) is of type L
-- this is like return type matching the type of the whole expr can be inferred to be L
-- 4. M:(λx:A.B)

-- Note that reduction happens in inference, too
-- as per 6. https://en.wikipedia.org/wiki/Calculus_of_constructions

def substitute (idx : ℕ) (with_expr : LExpr) : LExpr → LExpr
  | abstraction x bind_ty body => abstraction x (substitute idx with_expr bind_ty) (substitute idx with_expr body)
  | fall x bind_ty body => fall x (substitute idx with_expr bind_ty) (substitute idx with_expr body)
  | t@(ty _) => t
  | prp => prp
  | v@(bvar n) => if n == idx then with_expr else v
  | app lhs rhs =>
    app (substitute idx with_expr lhs) (substitute idx with_expr rhs)

def eval (e : LExpr) : Option LExpr :=
  match e with
    | app lhs rhs =>
      match eval lhs with
        | abstraction idx _ body => pure $ substitute idx rhs body
        | _ => none
    | x => pure x

structure Context where
  types : List $ ℕ × LExpr

def infer (e : LExpr) : StateT Context Option LExpr := do
  match e with
    | prp => pure $ ty 0
    | (ty n) => pure $ ty $ n + 1
    | (fall idx e_ty e_body)  =>
      -- Set type and normal form of bound vars with idx
      -- to the inferred type of e_ty
      let e_ty' ← infer e_ty

      StateT.modifyGet λctx => ⟨(),{ ctx with types := (idx, e_ty') :: ctx.types }⟩

      -- Use new inference rules to infer body type
      -- This is the type of the entire expression
      infer e_body
    | (abstraction idx e_ty e_body) =>
      -- Pretty similar thing to forall
      let norm_e_ty ← infer e_ty
      StateT.modifyGet λctx => ⟨(), { ctx with types := (idx, norm_e_ty) :: ctx.types }⟩

      pure $ fall idx norm_e_ty (← infer e_body)
    | app lhs rhs =>
      match ← infer lhs with
      | (fall idx bind_ty body) =>
        let ty_rhs ← infer rhs

        if ty_rhs != bind_ty then
          -- These are technically also the same if they are beta
          -- normally equivalent
          let ty_rhsβ := eval ty_rhs
          let bind_tyβ := eval bind_ty

          if ty_rhsβ != bind_tyβ then
            none

        pure $ substitute idx body rhs
      | _ => none
    | bvar idx =>
      let { types } ← StateT.get
      match types |> List.filter λx => idx == Prod.fst x with
      | (_, ty_var)::_ => pure ty_var
      | List.nil => none

