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

def obvious_reducibility_candidates (t : LExpr) : Set LExpr :=
  match t with
    | prp => { e | match e with
      | fall _ _ => true
      | var _ => true
      | _ => false }
    | ty 0 => { e | match e with
      | prp => true
      | var _ => true
      | _ => false }
    | ty (n + 1) => { e | match e with
      | ty n₂ => n₂ = n
      | var _ => true
      | _ => false }
    | fall _ _ => { e | match e with
      | abstraction _ _ => true
      | var _ => true
      | _ => false }
    | _ => { e | match e with | var _ => true | _ => false }

def t_well_behaved : Set LExpr := { t | match t with
  | prp => t = prp
  | ty n => t = ty n
  | fall a b => t = fall a b
  | _ => false }

def obviously_well_typed : LExpr → Option LExpr
  | prp => some $ ty 0
  | ty n => some (ty $ n + 1)
  | fall _ _ =>
    some prp
  | abstraction a b =>
    some $ fall a b
  | _ => none

def e_obviously_well_behaved : Set LExpr := { e | match e with
  | prp => true
  | ty _ => true
  | fall _ _ => true
  | abstraction _ _ => true
  | _ => false }

lemma all_obviously_well_typed_well_behaved (t : LExpr) (e : LExpr) : obviously_well_typed e = some t → e ∈ obvious_reducibility_candidates t
  | h => by
    simp [obviously_well_typed] at h
    unfold obvious_reducibility_candidates
    match h₂ : e with
      | prp =>
        have h₃ : t = ty 0 := by
          simp [*] at h
          simp_all
        simp_all
      | ty n =>
        simp_all
        have h₃ : t = (ty $ n + 1) := by
          simp [*] at h
          simp_all
        simp_all
      | fall _ _ =>
        have h₃ : t = prp := by
          simp [*] at h
          simp_all
        simp_all
      | abstraction a b =>
        have h₄ : t = fall a b := by
          simp [*] at h
          simp_all
        simp_all

def eval_same_type (f_ty : TypeContext) (e : LExpr) := f_ty (eval_once e) = f_ty e

def well_typed (f_ty : TypeContext) (e : LExpr) (_h_holds_obvious_typings : ∀ e, (obviously_well_typed e).isSome → f_ty e = obviously_well_typed e) := match e with
  | app lhs rhs =>
    (f_ty e).isSome ∧
    (Option.map₂ (λa b => (a, b)) (Option.map₂ (λa b => (a, b)) (f_ty lhs) (f_ty e)) (f_ty rhs) |>
      Option.map (λ((ty_lhs, ty_e), ty_rhs) => ty_lhs = fall ty_rhs ty_e)) = some true ∧
    well_typed f_ty lhs _h_holds_obvious_typings ∧
    well_typed f_ty rhs _h_holds_obvious_typings
  | e => (f_ty e).isSome ∧ ((f_ty e).map (. ∈ t_well_behaved)) = some true

theorem well_typed_well_behaved (f_ty : TypeContext) (t : LExpr) (e : LExpr) (h_holds_obvious_typings : ∀ e, (obviously_well_typed e).isSome → f_ty e = obviously_well_typed e) (h_well_typed : well_typed f_ty e h_holds_obvious_typings) (h_specifically_well_typed : f_ty e = some t) (h_eval_same_type : ∀ e, eval_same_type f_ty e): e ∈ obvious_reducibility_candidates t := by
  unfold obvious_reducibility_candidates
  unfold well_typed at h_well_typed
  match h : e with
    | prp =>
      have h₃ : t = ty 0 := by
        unfold obviously_well_typed at h_holds_obvious_typings
        simp_all
      simp_all
    | ty n =>
      have h₃ : t = (ty $ n + 1) := by
        unfold obviously_well_typed at h_holds_obvious_typings
        simp_all
      simp_all
    | fall _ _ =>
      have h₃ : t = prp := by
        unfold obviously_well_typed at h_holds_obvious_typings
        simp_all
      simp_all
    | abstraction a b =>
      have h₄ : t = fall a b := by
        unfold obviously_well_typed at h_holds_obvious_typings
        simp_all
      simp_all
    | var n =>
      simp_all
      unfold t_well_behaved at h_well_typed
      split
      simp
      rw [← h]
      simp
      rw [h]
      simp
      simp
      rw [← h]
      simp
      rw [h]
      simp
      rw [← h]
      simp
      rw [h]
      simp
    | app lhs rhs =>
      simp at h_well_typed
      have ⟨h₁, h₂, well_typed_lhs, well_typed_rhs⟩ := h_well_typed
      let ⟨ty_lhs, ⟨ty_e, ⟨ty_rhs, ⟨h_ty_lhs, h_ty_e, h_ty_rhs⟩, h_ty_lhs_fall⟩⟩⟩ := h₂
      have h_lhs_well_typed_well_behaved := well_typed_well_behaved f_ty ty_lhs lhs h_holds_obvious_typings well_typed_lhs h_ty_lhs
      have h_rhs_well_typed_well_behaved := well_typed_well_behaved f_ty ty_rhs rhs h_holds_obvious_typings well_typed_rhs h_ty_rhs
      let lhs' := substitute rhs lhs

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
      -- Therefore, the entire expression is well-behaved
      -- Since e ≠ app _ _, since it is in the reducibility candidates

      

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
