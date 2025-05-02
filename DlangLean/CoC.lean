import Mathlib.Data.Nat.Notation
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic
import Std.Data.HashMap.Basic

inductive LExpr where
  -- ty, body
  | abstraction : LExpr → LExpr → LExpr
  | fall        : LExpr → LExpr → LExpr
  -- T and P, CoC
  | ty          : ℕ → LExpr
  | prp         : LExpr
  -- De Bruijn Index
  -- Start at 0
  | var         : ℕ      → LExpr
  | app         : LExpr  → LExpr → LExpr
deriving BEq

open LExpr

def final : LExpr → Bool
  | abstraction _ _
  | fall _ _
  | ty _
  | prp
  | var _ => true
  | app _ _ => false

def map_indices_free (n_binders : ℕ) (f : ℕ → ℕ) : LExpr → LExpr
  | abstraction e_ty body => abstraction (map_indices_free n_binders.succ f e_ty) (map_indices_free n_binders.succ f body)
  | fall e_ty body => fall (map_indices_free n_binders.succ f e_ty) (map_indices_free n_binders.succ f body)
  | t@(ty _) => t
  | p@prp => p
  -- if bound, don't touch this
  | v@(var n) => if n ≥ n_binders then var (f n) else v
  | app lhs rhs => app (map_indices_free n_binders f lhs) (map_indices_free n_binders f rhs)

-- Note: cleaned this up a little with GPT-4o.
-- A couple bugs with debrujin indexing noticed. Fixed those.
-- Namely
--
-- When substituting an abstraction inside an abstraction, its free debrujin indices
-- should be incremented
def substitute (with_expr : LExpr) : LExpr → LExpr
  | (abstraction bind_ty body) =>
    let with_expr' := map_indices_free 0 (Nat.succ .) with_expr

    abstraction (substitute with_expr' bind_ty) (substitute with_expr' body)
  | fall bind_ty body =>
    let with_expr' := map_indices_free 0 (Nat.succ .) with_expr

    fall (substitute with_expr' bind_ty) (substitute with_expr' body)
  | t@(ty _) => t
  | prp => prp
  | var 0 => with_expr
  | var n => var $ n - 1
  | app lhs rhs =>
    app (substitute with_expr lhs) (substitute with_expr rhs)

-- The size of the type tree will strictly decrease
-- it literally cannot get bigger
-- This is how we do structural recursion
def eval_once : LExpr → LExpr
  | app (abstraction _ body) rhs =>
    substitute rhs body
  | app lhs rhs =>
    app (eval_once lhs) rhs
  | x => x

structure TypeContext where
  f_ty : LExpr → Option LExpr

  -- If an application is well-typed, then its lhs is type forall
  well_typed_app := ∀ lhs rhs, (f_ty $ app lhs rhs).isSome →
    match f_ty lhs with
      | some (fall _ _) => true
      | _ => false

  all_types_final := ∀ e, (f_ty e).isSome → (f_ty e).map final = some true

theorem well_typed_final (ctx : TypeContext) (e : LExpr) : (ctx.f_ty e).isSome → final e
  | h_well_typed => by
    match h : e with
      | var _
      | fall _ _
      | abstraction _ _
      | ty _
      | prp =>
        unfold final
        simp_all
      | app lhs rhs =>
        have h_abstr : match ctx.f_ty lhs with
             | some (fall _ _) => true
             | _ => false
          := sorry
        sorry

def eval (e : LExpr) (f_ty : TypeContext) (h_all_types_final : all_types_final f_ty) : ∃ e' : LExpr, final e' := by
  match h₁ : e with
    | app lhs rhs =>
      let ⟨lhs', h_lhs'_final⟩ := eval lhs f_ty (by simp_all)
      match h₂ : lhs' with
        | abstraction bind_ty body =>
          use substitute body rhs
          
          sorry
        | fall _ _ => sorry
        | app lhs rhs =>
          contradiction
        | var _ => sorry
        | ty _ => sorry
        | prp => sorry
    | a@(abstraction bind_ty body) =>
      use abstraction bind_ty body
      unfold final
      simp
    | fall bind_ty body =>
      use fall bind_ty body
      unfold final
      simp
    | var n =>
      use var n
      unfold final
      simp
    | ty n =>
      use ty n
      unfold final
      simp
    | prp =>
      use prp
      unfold final
      simp

/--def infer (dir_types : List $ List $ PathDirection LExpr) (e : LExpr) : Option (List $ PathDirection LExpr) :=
  do match e with
    | prp => pure $ pure $ leaf (ty 0)
    | ty n => pure $ pure $ leaf (ty $ n + 1)
    | fall e_ty e_body  =>
      -- Set type and normal form of bound vars with idx
      -- to the inferred type of e_ty
      let e_ty' ← infer dir_types e_ty

      let directions := [in_bind_ty e_ty']
      let directions' := in_body (← infer (directions :: dir_types) e_body) :: directions

      -- Use new inference rules to infer body type
      -- This is the type of the entire expression
      pure directions'
    | abstraction e_ty e_body =>
      -- Pretty similar thing to forall
      let norm_e_ty ← infer dir_types e_ty

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

          pure $ substitute body rhs
        | _ => none
    | var idx =>
      let types ← StateT.get
      types[idx]?

def type_of (e : LExpr) : List LExpr → Option LExpr := (Prod.fst <$> (infer e).run .)
--/

def bruh := ()
