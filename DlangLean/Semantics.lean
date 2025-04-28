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

def eval_infer (e : LExpr) : StateT (List $ (ℕ × (LExpr × LExpr))) Option (LExpr × LExpr) :=
  match e with
  | p@prp => pure $ (p, ty 0)
  | t@(ty n) => pure $ (t, (ty $ n + 1))
  | f@(fall idx e_ty e_body)  => do
    -- Set type and normal form of bound vars with idx
    -- to the inferred type of e_ty
    StateT.modifyGet (⟨(), (idx, ← eval_infer e_ty) :: .⟩)

    -- Use new inference rules to infer body type
    -- This is the type of the entire expression
    pure (f, (← eval_infer e_body).snd)
  | a@(abstraction idx e_ty e_body) => do
    -- Pretty similar thing to forall
    let norm_e_ty ← eval_infer e_ty
    StateT.modifyGet (⟨(), (idx, norm_e_ty) :: .⟩)

    pure $ (a, fall idx norm_e_ty.snd (← eval_infer e_body).snd)
  | app (fall idx bind_ty body) rhs => do
    let (norm_rhs, ty_rhs) ← eval_infer rhs

    -- These are technically also the same if they are beta
    -- normally equivalent
    if ty_rhs != (← eval_infer (bind_ty)).snd then
      none

    StateT.modifyGet (⟨(), (idx, (norm_rhs, ty_rhs)) :: .⟩)

    eval_infer body
  | bvar idx => do
    match (← StateT.get) |> List.filter λ(idx₂, _) => idx == idx₂ with
    | (_, (v, ty_var))::_ => pure (v, ty_var)
    | List.nil => none
  | _ => none


theorem strongly_normalizing
