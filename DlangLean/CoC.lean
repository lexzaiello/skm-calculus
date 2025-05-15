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

structure TypeContext where
  t_well_behaved : Set LExpr := { t | match t with
    | prp => t = prp
    | ty n => t = ty n
    | fall a b => t = fall a b
    | _ => false }

  t_well_behaved_def : t_well_behaved = { t | match t with
    | prp => t = prp
    | ty n => t = ty n
    | fall a b => t = fall a b
    | _ => false }

namespace TypeContext

def obviously_well_typed { ctx : TypeContext } (e : LExpr) : Option LExpr :=
    match e with
      | prp => some $ ty 0
      | ty n => some (ty $ n + 1)
      | fall _ body_ty =>
        ctx.obviously_well_typed body_ty
      | abstraction bind_ty body =>
        ctx.obviously_well_typed body |> Option.map (fall bind_ty .)
      | app lhs rhs => do
        let ty_lhs ← ctx.obviously_well_typed lhs
        let ty_rhs ← ctx.obviously_well_typed rhs

        match ty_lhs with
          | fall bind_ty body_ty =>
            if ty_rhs == bind_ty then
              some body_ty
            else
              none
          | _ => none
      | _ => none

def obvious_reducibility_candidates { ctx : TypeContext } (t : LExpr) : Set LExpr :=
  match t with
    | prp => { e | match e with
      | fall a b => e = fall a b
      | var n => e = var n
      | _ => false }
    | ty 0 => { e | match e with
      | prp => e = prp
      | var n => e = var n
      | _ => false }
    | ty (n + 1) => { e | match e with
      | ty n₂ => n₂ = n
      | var n => e = var n
      | _ => false }
    | fall bind_ty body_ty =>
      let candidates_bind_ty := ctx.obvious_reducibility_candidates bind_ty
      let candidates_body_ty := ctx.obvious_reducibility_candidates body_ty

      { e |
        match e with | var _ => true | _ => false
      } ∪ { e : LExpr |
        match e with
          | abstraction _ _ =>
            ∀ u ∈ candidates_bind_ty, (eval_once $ app e u) ∈ candidates_body_ty
          | _ => false }
    | _ => { e | match e with | var _ => true | _ => false }

lemma all_app_same_type { ctx : TypeContext } (t e : LExpr) : ctx.obviously_well_typed e = some t → ctx.obviously_well_typed (eval_once e) = some t := by
  intro h_obv_typed
  have h_obv_typed₂ := h_obv_typed
  unfold obviously_well_typed at h_obv_typed
  simp at h_obv_typed₂
  match e with
    | prp =>
      unfold eval_once
      unfold obviously_well_typed
      simp
      simp_all
    | ty n =>
      unfold eval_once
      unfold obviously_well_typed
      simp
      simp_all
    | var n =>
      simp at h_obv_typed
    | fall _ _ =>
      unfold eval_once
      unfold obviously_well_typed
      simp
      simp at h_obv_typed
      simp_all
    | abstraction _ _ =>
      unfold eval_once
      unfold obviously_well_typed
      simp
      simp at h_obv_typed
      simp_all
    | app (abstraction bind_ty body) rhs =>
      -- Lhs must be an abstraction
      -- otherwise, evaluation does nothing
      -- Furthermore, since the expression is obviously well-typed,
      -- the type of the right hand side = bind_ty
      -- and the type of body = type of expression
      -- We know the type of the whole expression
      rw [← h_obv_typed₂]
      unfold eval_once
      unfold substitute
      
    | app lhs rhs => sorry

lemma all_reducibility_candidates_strongly_normalizing {ctx : TypeContext} : ∀ t e, e ∈ ctx.obvious_reducibility_candidates t → is_strongly_normalizing e := sorry

-- If an abstraction is well-typed, it is in R(fall bind_ty body_ty)
lemma all_well_typed_abstractions_well_typed_args_in_reducibility_candidates { ctx : TypeContext } (t e : LExpr) (e_is_abstraction : match e with | abstraction _ _ => true | _ => false) (t_is_fall : match t with | fall _ _ => true | _ => false) : ctx.f_ty e = some t → ctx.is_well_typed t e → e ∈ ctx.obvious_reducibility_candidates t := by
  intro h_is_type h_well_typed
  unfold obvious_reducibility_candidates
  unfold is_well_typed at h_well_typed
  simp at h_well_typed
  simp
  match h : t with
    | fall bind_ty body_ty =>
      simp
      split
      simp
      simp
      match h₁ : e with
        | abstraction bind_ty' body =>
          simp at h_well_typed
          simp
          intro u h_u_in_r
          unfold obvious_reducibility_candidates
          match body_ty with
            | prp =>
              simp_all
              
              sorry
            | ty n => sorry
            | fall _ _ => sorry
            | abstraction _ _ => sorry
            | app lhs rhs => sorry
            | var _ => sorry

theorem well_typed_well_behaved
  { ctx : TypeContext }
  (t : LExpr)
  (e : LExpr)
  (h_well_typed : ctx.is_well_typed t e)
  (h_is_type : some t = ctx.f_ty e)
    : e ∈ ctx.obvious_reducibility_candidates t := by
    unfold TypeContext.obvious_reducibility_candidates
    have h_holds_obvious_typings := ctx.holds_obvious_typings
    rw [TypeContext.obviously_well_typed_def] at h_holds_obvious_typings
    simp at h_holds_obvious_typings
    match h : e with
      | prp =>
        have h₃ : ctx.f_ty prp = ty 0 := by
          simp [h_holds_obvious_typings prp]
        have h₄ : t = ty 0 := by
          simp_all
        simp [h₄]
      | ty n =>
        have h₃ : ctx.f_ty (ty n) = ty (n + 1) := by
          simp [h_holds_obvious_typings $ ty n]
        have h₄ : t = ty (n + 1) := by
          simp_all
        simp [h₄]
      | fall a b =>
        have h₃ : ctx.f_ty (fall a b) = prp := by
          simp [h_holds_obvious_typings $ (fall a b)]
        have h₄ : t = prp := by
          simp_all
        simp [h₄]
      | abstraction a b =>
        sorry
      | var n =>
        split
        simp
        simp
        simp
        simp
        simp
      | app lhs rhs =>
      -- The varible being bound in the lhs substitution is necessarily in obvious_reducibility_candidates
      -- This means it cannot be an application
      -- After substitution, it is possible that lhs will contain more applications
      -- Lhs must be of type prop. Otherwise, it cannot be applied
      -- Furthermore, lhs is well-behaved, so its body must also be well-behaved
      -- f_ty eval_once e = f_ty lhs.body
      -- lhs.body is surely well-behaved
      -- So, therefore, the whole expression is well-behaved
      -- We will need to take the assumption that the type of an expression stays the same after evaluation

      -- Since lhs is of type forall, it must be some expression in the reducibility candidates
      -- for type forall
      -- This could be any abstraction
      -- Thus, it is well-behaved
      --
      -- We will need to use induction somewhere by recursing
      -- Where will that be?
      -- If substitution produces no more applications, then we can say
      -- that the expression `e` is in the reducibility candidates
      -- There are two cases here:
      -- - The easy case, where substitution produces no more applications
      -- - And the recursive case where it produces a new application
      --   - We can't just recurse, since we need some decreasing factor
      -- The right hand side of an application is well-behaved, since it is well-typed
      -- We can show this inductively
      -- Therefore, the right hand side necessarily is not an application
        sorry

end TypeContext

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
