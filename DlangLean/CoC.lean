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

def map_indices_free (n_binders : ℕ) (f : ℕ → ℕ) : LExpr → LExpr
  | abstraction e_ty body => abstraction (map_indices_free n_binders.succ f e_ty) (map_indices_free n_binders.succ f body)
  | fall e_ty body => fall (map_indices_free n_binders.succ f e_ty) (map_indices_free n_binders.succ f body)
  | t@(ty _) => t
  | p@prp => p
  -- if bound, don't touch this
  | v@(var n) => if n ≥ n_binders then var (f n) else v
  | app lhs rhs => app (map_indices_free n_binders f lhs) (map_indices_free n_binders f rhs)

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

inductive beta_normal : LExpr → LExpr → Prop
  | trivial e      : eval_once e = e → beta_normal e e
  | hard (e₁ e₂ e₃ : LExpr) : eval_once e₁ = e₂ → beta_normal e₂ e₃ → beta_normal e₁ e₃

inductive is_strongly_normalizing : LExpr → Prop
  | trivial (e : LExpr) : eval_once e = e → is_strongly_normalizing e
  | hard    (e : LExpr) : is_strongly_normalizing (eval_once e) → is_strongly_normalizing e

def TypeContext := LExpr → Option LExpr

def well_typed (f_ty : TypeContext) (e : LExpr) := ∃ ty, f_ty e = some ty

def obvious_reducibility_candidates (t : LExpr) : ∃ s : Set LExpr, ∀ e, e ∈ s → is_strongly_normalizing e :=
  match t with
    | prp => ⟨setOf (match . with
      | fall _ _ => True
      | ty 0 => True
      | _ => false), λ e h_e => is_strongly_normalizing.trivial e (by
        unfold eval_once
        match e with
          | fall _ _ => simp_all
          | ty _ => simp_all
      )⟩
    | ty n => ⟨setOf (match . with
      | ty n₂ => n₂ = n + 1
      | _ => false), λ e h_e => is_strongly_normalizing.trivial e (by
        unfold eval_once
        match e with
          | ty _ => simp_all
      )⟩
    | fall _ _ => ⟨setOf (match . with
      | abstraction _ _ => true
      | _ => false), λ e h_e => is_strongly_normalizing.trivial e (by
        unfold eval_once
        match e with
          | abstraction _ _ => simp_all
      )⟩
    | _ => ⟨setOf (Function.const _ false), λ e h_e => by simp_all⟩

-- Expressions that strongly normalize that are of type t
def reducibility_candidates (t : LExpr) : ∃ s : Set LExpr, ∀ e, e ∈ s → is_strongly_normalizing e :=
  -- Anything of type Prop has an obvious candidate: ∀
  -- So does ty n
  -- And so does anything of type ∀ (e.g., λ)
  let obv_candidates := match t with
    | prp => setOf (match . with
      | fall _ _ => True
      | ty 0 => True
      | _ => false)
    | ty n => setOf (match . with
      | ty n₂ => n₂ = n + 1
      | _ => false)
    | fall _ _ => setOf (match . with
      | abstraction _ _ => true
      | _ => false)
    | _ => setOf (Function.const _ false)

  -- For other cases, we must use induction to find the reducibility set

  sorry

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
