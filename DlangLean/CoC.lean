import Mathlib.Tactic

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

inductive beta_normal : LExpr → Prop
  | trivial e   : eval_once e = e           → beta_normal e
  | hard e      : beta_normal (eval_once e) → beta_normal e

inductive beta_eq : LExpr → LExpr → Prop
  | trivial e₁ e₂    : e₁ = e₂  → beta_eq e₁ e₂
  | right   e₁ e₂    : e₁ ≠ e₂  → beta_eq e₁ (eval_once e₂) → beta_eq e₁ e₂
  | left    e₁ e₂    : e₁ ≠ e₂  → beta_eq (eval_once e₁) e₂ → beta_eq e₁ e₂

inductive is_strongly_normalizing : LExpr → Prop
  | trivial (e : LExpr) : eval_once e = e → is_strongly_normalizing e
  | hard    (e : LExpr) : is_strongly_normalizing (eval_once e) → is_strongly_normalizing e

def t_well_behaved : Set LExpr := { t | match t with
    | prp => t = prp
    | ty n => t = ty n
    | fall a b => t = fall a b
    | _ => false }

def obvious_type_inference (e : LExpr) : Option LExpr :=
    match e with
      | prp => some $ ty 0
      | ty n => some (ty $ n + 1)
      | fall _ body_ty =>
        obvious_type_inference body_ty
      | abstraction bind_ty body => do
        pure $ fall bind_ty (← obvious_type_inference body)
      | app lhs rhs => do
        let ty_lhs ← obvious_type_inference lhs
        let ty_rhs ← obvious_type_inference rhs

        match ty_lhs with
          | fall bind_ty body_ty =>
            if ty_rhs == bind_ty then
              some (substitute body_ty rhs)
            else
              none
          | _ => none
      | _ => none

def obvious_reducibility_candidates (t : LExpr) : Set LExpr :=
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
      let candidates_bind_ty := obvious_reducibility_candidates bind_ty
      let candidates_body_ty := obvious_reducibility_candidates body_ty

      { e |
        match e with | var _ => true | _ => false
      } ∪ { e : LExpr |
        match e with
          | abstraction _ _ =>
            ∀ u ∈ candidates_bind_ty, (eval_once $ app e u) ∈ candidates_body_ty
          | _ => false }
    | _ => { e | match e with | var _ => true | _ => false }

def obv_valid_judgements (e : LExpr) : Set LExpr := match e with
    | prp => { ty 0 }
    | ty n => { ty $ n + 1 }
    | fall _ body_ty =>
      obv_valid_judgements body_ty
    | abstraction bind_ty body =>
      { t | ∃ body_ty, beta_eq t (fall bind_ty body_ty) ∧ t ∈ obv_valid_judgements body }
    | app lhs rhs =>
      { t | ∃ ty_rhs, ty_rhs ∈ obv_valid_judgements rhs ∧ (fall (ty_rhs) t) ∈ obv_valid_judgements lhs }
    | var _ => { _t | true }

def valid_typing_judgements (e : LExpr) : Set LExpr :=
  { t | t ∈ obv_valid_judgements e ∧ (∀ t', beta_eq t t' ↔ t' ∈ obv_valid_judgements e) }

lemma eval_beta_eq (e : LExpr) : beta_eq (eval_once e) e := by
  if h : eval_once e = e then
    rw [h]
    exact beta_eq.trivial e e rfl
  else
    exact beta_eq.right (eval_once e) e h $ beta_eq.trivial (eval_once e) (eval_once e) rfl

lemma overlap_typing_judgements_beta_eq_t (t t₁ : LExpr) : ∀ e, t ∈ valid_typing_judgements e → t₁ ∈ valid_typing_judgements e → beta_eq t t₁ := by
  intro e h_t_judgement₁ h_t_judgement₂
  unfold valid_typing_judgements at *
  simp_all

-- If two types are beta equivalent,
-- then we can say that they are eventually
-- definitionally equivalent after some sequence of reductions
--
-- However, we can't easily do induction on this, since this is unfounded recursion
-- However, if we somehow change the goal to proving that t and t₂ are beta_equivalent
-- then we can construct the inductive case to solve our goal
-- We can use our overlap_typing_judgements_beta_eq_t lemma
-- If we can prove that the two types are beta normal, then we can prove the goal
--
-- have h := beta_eq_t_overlap_typing_judgements t t₂ sorry sorry
-- this tells us that if e is in both of the typing judgements, then the types are the same
-- we can prove this in two cases:
-- t₁ is clearly a proper typing judgement for *something*. Perhaps not e, but an e₂
-- there a couple cases:
-- e is contained by e₂
-- e₂ is contained in e
-- e₂ = e (easy case)
--
--Note that the only case in which evaluation does not produce the same term is application
-- our definition of the typing judgement defines application as producing the same type

lemma eval_once_noop_not_app (e : LExpr) (h_not_app : match e with | app _ _ => false | _ => true) : eval_once e = e := by
  match e with
    | var _ =>
      unfold eval_once
      rfl
    | ty _ =>
      unfold eval_once
      rfl
    | app _ _ =>
      contradiction
    | prp =>
      unfold eval_once
      rfl
    | fall _ _ =>
      unfold eval_once
      rfl
    | abstraction _ _ =>
      unfold eval_once
      rfl

lemma substitute_judgement_holds (t bind_ty body : LExpr) : t ∈ valid_typing_judgements (abstraction bind_ty body) → ∀ e, bind_ty ∈ valid_typing_judgements e → t ∈ valid_typing_judgements (substitute e $ abstraction bind_ty body) := sorry

lemma eval_once_judgement_holds (t e) : t ∈ valid_typing_judgements e → t ∈ valid_typing_judgements (eval_once e) := by
  -- Easy cases are where e is not an application, since eval is a noop
  match h : e with
    | app lhs rhs =>
      intro ht
      unfold eval_once
      unfold valid_typing_judgements at *
      unfold obv_valid_judgements at *
      have ⟨⟨ty_rhs, ⟨h_ty_rhs, h_ty_lhs⟩⟩, h_all_eq_types⟩ := ht
      constructor
      -- Now, we know that the type of lhs body = t and ty_rhs = bind_ty
      -- We can say that the expression reduces to body pretty easily
      match h' : lhs with
        | abstraction bind_ty body =>
          have h'' := substitute_judgement_holds t ty_rhs body (by sorry) body
          sorry
        | lhs => sorry
      sorry
    | var n =>
      have h : eval_once (var n) = (var n) := eval_once_noop_not_app (var n) (by simp)
      simp_all
    | ty n =>
      have h : eval_once (ty n) = (ty n) := eval_once_noop_not_app (ty n) (by simp)
      simp_all
    | prp =>
      have h : eval_once prp = prp := eval_once_noop_not_app prp (by simp)
      simp_all
    | fall a b =>
      have h : eval_once (fall a b) = (fall a b) := eval_once_noop_not_app (fall a b) (by simp)
      simp_all
    | abstraction a b =>
      have h : eval_once (abstraction a b) = (abstraction a b) := eval_once_noop_not_app (abstraction a b) (by simp)
      simp_all

lemma beta_eq_judgement_holds_not_app (t e e' : LExpr) (h_not_app : match e with | app _ _ => false | _ => true) (h_not_app₂ : match e' with | app _ _ => false | _ => true) : beta_eq e e' → t ∈ valid_typing_judgements e → t ∈ valid_typing_judgements e' := by
  intro h_beta_eq valid_t_judgement
  unfold valid_typing_judgements at *
  have h_e_eval_noop : eval_once e = e := eval_once_noop_not_app e h_not_app
  have h_e_eval_noop' : eval_once e' = e' := eval_once_noop_not_app e' h_not_app₂
  -- Beta reduction for something that is not an application deos NOTHING
  -- Thus, if two things are beta equivalent that do not reduce to anything else
  -- they must be definitionally equivalent

  match h₃ : h_beta_eq with
    | beta_eq.trivial lhs rhs h_rfl_eq =>
      simp_all
    | beta_eq.right e e' h_neq eval_eq =>
      simp_all
      constructor
      simp_all
      -- beta_eq e e₁ ∧ e ≠ e₁ → ¬beta_eq.trivial e e₁ → beta_eq.left e e₁ ∨ beta_eq.right e e₁
      -- HOWEVER
      -- evaluation not doing anything throws a big loop in this, since
      -- beta_eq.left relies on it:
      -- beta_eq.left implies at some poin tthat 
      
      sorry
    | beta_eq.left e e' h_neq eval_eq => sorry

lemma beta_eq_judgement_holds (t t₁ e : LExpr) : ∀ e', beta_eq e e' ∧ beta_eq e' e → t ∈ valid_typing_judgements e → t₁ ∈ valid_typing_judgements e' → t ∈ valid_typing_judgements e' := by
  intro e' ⟨beq_lhs, beq_rhs⟩ h₂ h₃
  match beq_lhs with
    | beta_eq.trivial e e' h_rfl =>
      rw [← h_rfl]
      exact h₂
    | beta_eq.trans e e' e₃ h_beq_1 h_beq_2 =>
      sorry
    | beta_eq.left e e' h_left =>
      -- Important case: bera normal evaluation is the same type
      -- we can show this easily for expressions that are beta normal
      -- and evaluation does nothing
      
      sorry
    | beta_eq.right e e' h_right => sorry
    | beta_eq.symm e e' h_symm => sorry

lemma beta_eq_same_type (t t₁ e e₁ : LExpr) : t ∈ valid_typing_judgements e ∧ t₁ ∈ valid_typing_judgements e₁ → beta_eq e e₁ ∧ beta_eq e₁ e → beta_eq t t₁
  | ⟨⟨lhs₁, lhs₂⟩, ⟨rhs₁, rhs₂⟩⟩, ⟨h_beta_eq_left, h_beta_eq_right⟩ => by
    
    sorry

lemma all_app_same_type (t e : LExpr) : verify_typing_judgement e t → verify_typing_judgement (eval_once e) t := by
  intro h_judgement_true
  have h_judgement_true₂ := h_judgement_true
  match e with
    | prp =>
      unfold eval_once
      unfold verify_typing_judgement at *
      exact h_judgement_true
    | ty n =>
      unfold eval_once
      unfold verify_typing_judgement at *
      exact h_judgement_true
    | var n =>
      unfold eval_once
      unfold verify_typing_judgement at *
      exact h_judgement_true
    | fall _ _ =>
      unfold eval_once
      unfold verify_typing_judgement at *
      exact h_judgement_true
    | abstraction _ _ =>
      unfold eval_once
      unfold verify_typing_judgement at *
      exact h_judgement_true
    | app lhs rhs =>
      unfold verify_typing_judgement at h_judgement_true
      unfold verify_typing_judgement
      have ⟨rhs_ty, lhs_is_fall_ty, rhs_ty_is_rhs_ty⟩ := h_judgement_true
      split
      case h_1 e heq =>
        have h_prp_beq_eval : beta_eq prp (eval_once (app lhs rhs)) := beta_eq.trivial prp (eval_once (app lhs rhs)) (Eq.symm heq)
        
      sorry

lemma all_reducibility_candidates_strongly_normalizing : ∀ t e, e ∈ ctx.obvious_reducibility_candidates t → is_strongly_normalizing e := sorry

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
