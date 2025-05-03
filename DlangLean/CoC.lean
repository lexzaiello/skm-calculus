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

def trivially_strongly_normalizing (e : LExpr) := match e with
    | app _ _ => false
    | _ => true

inductive beta_normal : LExpr → LExpr → Prop
  | trivial e     : beta_normal e e
  | hard (e₁ e₂ e₃ : LExpr) : eval_once e₁ = e₂ → beta_normal e₂ e₃ → beta_normal e₁ e₃

theorem beta_normal_eval_once : ∀ e : LExpr, beta_normal e (eval_once e)
  | e => beta_normal.hard e (eval_once e) (eval_once e) rfl (beta_normal.trivial (eval_once e))

theorem beta_normal_id : ∀ e, beta_normal e e := beta_normal.trivial

structure TypeContext where
  f_ty : LExpr → Option LExpr

  well_typed (e : LExpr) := (f_ty e).isSome = true

  -- If an application is well-typed, then its lhs is type forall
  well_typed_app' (e : LExpr) (ty : LExpr) (h_ty_correct : f_ty e = some ty) : match e with
    | app lhs rhs =>
      ∃ bind_ty body, f_ty rhs = some bind_ty ∧ f_ty body = some ty ∧ f_ty lhs = some (fall bind_ty body)
    | _ => true

inductive is_strongly_normalizing (ctx : TypeContext) : LExpr → Prop
  | trivial (e : LExpr) : trivially_strongly_normalizing e → is_strongly_normalizing ctx e
  | hard (e : LExpr) : is_strongly_normalizing ctx (eval_once e) → is_strongly_normalizing ctx e

def strongly_normalizing (ctx : TypeContext) (e : LExpr) (ty : LExpr) (h_ty_correct : ctx.f_ty e = some ty) : is_strongly_normalizing ctx e :=
    match h : e with
      | var a =>
        @is_strongly_normalizing.trivial ctx (var a) (by
          unfold trivially_strongly_normalizing
          simp
        )
      | fall bind_ty body =>
        @is_strongly_normalizing.trivial ctx (fall bind_ty body) (by
          unfold trivially_strongly_normalizing
          simp
        )
      | abstraction bind_ty body => @is_strongly_normalizing.trivial ctx (abstraction bind_ty body) (by
          unfold trivially_strongly_normalizing
          simp
        )
      | LExpr.ty n => @is_strongly_normalizing.trivial ctx (LExpr.ty n) (by
          unfold trivially_strongly_normalizing
          simp
        )
      | prp => @is_strongly_normalizing.trivial ctx prp (by
          unfold trivially_strongly_normalizing
          simp
        )
      | app lhs rhs => by
        have h_app_maybe_well_typed := ctx.well_typed_app' (app lhs rhs) ty h_ty_correct
        simp at h_app_maybe_well_typed

        have ⟨bind_ty, ⟨h_bind_ty, ⟨body, ⟨h_ty_body, h_ty_lhs⟩⟩⟩⟩ := h_app_maybe_well_typed

        have h_lhs_strongly_normalizing : is_strongly_normalizing ctx lhs := strongly_normalizing ctx lhs (fall bind_ty body) (by simp [h_ty_lhs])
        have h_rhs_strongly_normalizing : is_strongly_normalizing ctx rhs := strongly_normalizing ctx rhs bind_ty (by simp [h_bind_ty])

        -- Given left hand side and right hand side are strongly normalizing, then
        -- the whole substitution is strongly normalizing
        --
        -- This is because the left hand side being strongly normalizing
        -- means it is beta equivalent to one of the trivially normalizing exprs
        exact @is_strongly_normalizing.hard ctx (app lhs rhs) (by
          
          unfold eval_once

          match app lhs rhs with
          | app (abstraction bind_ty body) rhs =>
            simp
            
            sorry
          | app lhs rhs => sorry
          | abstraction  bind_ty body =>
            simp
            exact is_strongly_normalizing.trivial (abstraction bind_ty body) (by
              unfold trivially_strongly_normalizing
              simp
            )
          | var n =>
            simp
            exact is_strongly_normalizing.trivial (var n) (by
              unfold trivially_strongly_normalizing
              simp
            )
          | LExpr.ty n =>
              simp
              exact is_strongly_normalizing.trivial (LExpr.ty n) (by
                unfold trivially_strongly_normalizing
                simp
              )
            | prp =>
              simp
              exact is_strongly_normalizing.trivial prp (by
                unfold trivially_strongly_normalizing
                simp
              )
            | fall bind_ty body =>
              simp
              exact is_strongly_normalizing.trivial (fall bind_ty body) (by
                unfold trivially_strongly_normalizing
                simp
              )
        )

/--def eval (e : LExpr) (f_ty : TypeContext) : ∃ e' : LExpr, final e' := by
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

def infer (dir_types : List $ List $ PathDirection LExpr) (e : LExpr) : Option (List $ PathDirection LExpr) :=
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
