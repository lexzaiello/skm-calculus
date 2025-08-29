import Mathlib.Tactic

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | arr  : Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat skmexpr
syntax "K"                     : skmexpr
syntax "S"                     : skmexpr
syntax "M"                     : skmexpr
syntax "#~>"                   : skmexpr
syntax skmexpr "~>" skmexpr    : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax ident                   : skmexpr
syntax "#" term                : skmexpr
syntax "(" skmexpr ")"         : skmexpr

syntax " ⟪ " skmexpr " ⟫ "     : term
syntax "SKM[ " skmexpr " ] "   : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K ⟫)                           => `(Expr.k)
  | `(⟪ S ⟫)                           => `(Expr.s)
  | `(⟪ M ⟫)                           => `(Expr.m)
  | `(⟪ #~> ⟫)                         => `(Expr.arr)
  | `(⟪ $e₁:skmexpr ~> $e₂:skmexpr ⟫)  => `(Expr.call (Expr.call Expr.arr ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)   => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

inductive is_eval_once : Expr → Expr → Prop
  | k        : is_eval_once SKM[((((K _t_x) _t_y) x) y)] x
  | s        : is_eval_once SKM[((((((S _t_x) _t_y) _t_z) x) y) z)] SKM[((x z) (y z))]
  | k_call   : is_eval_once SKM[(((M K) α) β)] SKM[(α ~> (β ~> α))]
  | s_call   : is_eval_once SKM[((((M S) α) β) γ)] SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | m_call   : is_eval_once SKM[(M (lhs rhs))] SKM[((M lhs) rhs)]
  | arr_call : is_eval_once SKM[(((M #~>) t_in) t_out)] SKM[(t_in ~> (M t_out))]
  | arr      : is_eval_once SKM[((t_in ~> t_out) arg)] SKM[t_out]
  | left     : is_eval_once lhs lhs'
    → is_eval_once SKM[(lhs rhs)] SKM[(lhs' rhs)]

inductive is_eval_step : Expr → Expr → Prop
  | step  : is_eval_once e e'
    → is_eval_step e e'
  | trans : is_eval_step e e'
    → is_eval_step e' e''
    → is_eval_step e e''
  | rfl : is_eval_step e e

inductive is_eval_step_once : Expr → Expr → Prop
  | left : is_eval_once lhs lhs'
    → is_eval_step_once SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | step : is_eval_once e e'
    → is_eval_step_once e e'

inductive beta_eq : Expr → Expr → Prop
  | eval  : is_eval_once e₁ e₂ → beta_eq e₁ e₂
  | left  : beta_eq lhs lhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right : beta_eq rhs rhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')]
  | trans : beta_eq e₁ e₂      → beta_eq e₂ e₃ → beta_eq e₁ e₃
  | symm  : beta_eq e₁ e₂      → beta_eq e₂ e₁
  | rfl   : beta_eq e e

inductive is_value : Expr → Prop
  | k     : is_value SKM[K]
  | s     : is_value SKM[S]
  | m     : is_value SKM[M]
  | m_k   : is_value SKM[(M K)]
  | m_s   : is_value SKM[(M S)]
  | m_m   : is_value SKM[(M M)]
  | arr   : is_value SKM[(α ~> β)]
  | arr₁  : is_value SKM[(#~> α)]
  | arr₀  : is_value SKM[(#~>)]
  | m_arr : is_value SKM[(M #~>)]
  | k₁    : is_value SKM[(K α)]
  | k₂    : is_value SKM[((K α) β)]
  | k₃    : is_value SKM[(((K α) β) x)]
  | s₁    : is_value SKM[(S α)]
  | s₂    : is_value SKM[((S α) β)]
  | s₃    : is_value SKM[(((S α) β) γ)]
  | s₄    : is_value SKM[((((S α) β) γ) x)]
  | s₅    : is_value SKM[(((((S α) β) γ) x) y)]
  | m_k₁  : is_value SKM[((M K) α)]
  | m_s₁  : is_value SKM[((M S) α)]
  | m_s₂  : is_value SKM[(((M S) α) β)]

inductive is_value_n : ℕ → Expr → Expr → Prop
  | value : is_value e        → is_value_n 0 e e
  | succ  : is_eval_step e e' → is_value_n n e' e_final → is_value_n n.succ e e_final

inductive is_comb : Expr → Prop
  | k   : is_comb SKM[K]
  | s   : is_comb SKM[S]
  | m   : is_comb SKM[M]
  | arr : is_comb SKM[#~>]

inductive valid_judgment : Expr → Expr → Prop
  | comb₀     : is_comb e → valid_judgment e SKM[(M e)]
  | comb_call : valid_judgment lhs t_lhs
    → valid_judgment rhs t_rhs
    → (¬ ∃ t', is_eval_once SKM[(t_lhs rhs)] t')
    → valid_judgment SKM[(lhs rhs)] SKM[(t_lhs rhs)]
  | k         : valid_judgment α t_α
    → valid_judgment β t_β
    → valid_judgment SKM[((K α) β)] SKM[(α ~> (β ~> α))]
  | s         : valid_judgment α t_α
    → valid_judgment β t_β
    → valid_judgment γ t_γ
    → valid_judgment SKM[(((S α) β) γ)] SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | arr       : valid_judgment α t_α
    → valid_judgment β t_β
    → valid_judgment SKM[(α ~> β)] SKM[(α ~> t_β)]
  | call      : valid_judgment lhs SKM[(t_in ~> t_out)]
    → valid_judgment rhs t_in
    → valid_judgment SKM[(lhs rhs)] SKM[t_out]

inductive valid_judgment_hard : Expr → Expr → Prop
  | comb₀     : is_comb e → valid_judgment_hard e SKM[(M e)]
  | comb_call : valid_judgment_hard lhs t_lhs
    → valid_judgment_hard rhs t_rhs
    → (¬ ∃ t', is_eval_once SKM[(t_lhs rhs)] t')
    → valid_judgment_hard SKM[(lhs rhs)] SKM[(t_lhs rhs)]
  | k         : valid_judgment_hard α t_α
    → valid_judgment_hard β t_β
    → valid_judgment_hard SKM[((K α) β)] SKM[(α ~> (β ~> α))]
  | s         : valid_judgment_hard α t_α
    → valid_judgment_hard β t_β
    → valid_judgment_hard γ t_γ
    → valid_judgment_hard SKM[(((S α) β) γ)] SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | arr       : valid_judgment_hard α t_α
    → valid_judgment_hard β t_β
    → valid_judgment_hard SKM[(α ~> β)] SKM[(α ~> t_β)]
  | call      : valid_judgment_hard lhs SKM[(t_in ~> t_out)]
    → valid_judgment_hard rhs t_in
    → valid_judgment_hard SKM[(lhs rhs)] SKM[t_out]
  | step  : valid_judgment_hard e t
    → beta_eq t t'
    → valid_judgment_hard e t'

def is_typed_comb (e t : Expr) := valid_judgment e t ∧ ¬ ∃ t', is_eval_once t t'

namespace is_typed_comb

lemma well_typed : is_comb e → valid_judgment e SKM[(M e)] := valid_judgment.comb₀

end is_typed_comb

@[simp]
lemma m_stuck : is_value_n 0 SKM[M] SKM[M] := by
  apply is_value_n.value
  exact is_value.m

@[simp]
lemma k_stuck : is_value_n 0 SKM[K] SKM[K] := by
  apply is_value_n.value
  exact is_value.k

@[simp]
lemma s_stuck : is_value_n 0 SKM[S] SKM[S] := by
  apply is_value_n.value
  exact is_value.s

namespace is_eval_step

@[simp]
lemma do_step (h : is_eval_once e e') : is_eval_step e e' := is_eval_step.step h

lemma imp_beta_eq : is_eval_step e e' → beta_eq e e' := by
  intro h_step
  induction h_step
  case step lhs lhs' rhs =>
    exact beta_eq.eval rhs
  apply beta_eq.trans
  assumption
  assumption
  exact beta_eq.rfl

end is_eval_step

namespace is_eval_once

lemma no_step (h : ¬ ∃ e', is_eval_once SKM[(lhs rhs)] e') : ¬ ∃ lhs', is_eval_once lhs lhs' := by
  intro ⟨lhs', h⟩
  have h : is_eval_once SKM[(lhs rhs)] SKM[(lhs' rhs)] := is_eval_once.left h
  simp_all

end is_eval_once

namespace beta_eq

@[simp]
lemma go_left : beta_eq lhs lhs' → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)] := by
  apply beta_eq.left

@[simp]
lemma go_right : beta_eq rhs rhs' → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')] := by
  apply beta_eq.right

end beta_eq

namespace is_value

lemma no_step (h : is_value e) : ¬ ∃ e', is_eval_once e e' := by
  induction h
  repeat (intro e'; cases e'; contradiction)

lemma value_lhs (h : is_value SKM[(lhs rhs)]) : is_value lhs := by
  cases h
  exact is_value.m
  exact is_value.m
  exact is_value.m
  exact is_value.arr₁
  exact is_value.arr₀
  exact is_value.m
  exact is_value.k
  exact is_value.k₁
  exact is_value.k₂
  exact is_value.s
  exact is_value.s₁
  exact is_value.s₂
  exact is_value.s₃
  exact is_value.s₄
  exact is_value.m_k
  exact is_value.m_s
  exact is_value.m_s₁

end is_value

namespace valid_judgment

/-
Ugliest proof I have ever done. Fix this.
-/
lemma deterministic (h_t₁ : valid_judgment e t₁) (h_t₂ : valid_judgment e t₂) : t₁ = t₂ := by
  induction h_t₁ generalizing t₂
  case comb₀ e' h_comb =>
    cases h_comb
    repeat (cases h_t₂; rfl)
  case comb_call lhs t_lhs rhs t_rhs h_t_lhs h_t_rhs h_no_t_step ih₁ ih₂ =>
    cases h_t₂
    contradiction
    case comb_call t_lhs' t_rhs' h_t_lhs' h_t_rhs' h_no_t_step' =>
      rw [ih₁ h_t_lhs']
    cases h_t_lhs
    contradiction
    case k.comb_call α _ _ _ _ _ _ h _ _ =>
      cases h
      have h_yes_step : is_eval_once SKM[(((M K) α) rhs)] SKM[(α ~> (rhs ~> α))] := is_eval_once.k_call
      simp_all
    contradiction
    cases h_t_lhs
    contradiction
    case s.comb_call α t_α β t_β t_γ h_t_α h_t_β h_t_rhs t_lhs' t_rhs' h_t_left h_t_right h_no_step =>
      cases h_t_left
      contradiction
      case comb_call h_t_s h_t_α _ =>
        cases h_t_s
        have h_yes_step : is_eval_once SKM[((((M S) α) β) rhs)] SKM[((α ~> (β ~> rhs)) ~> ((α ~> β) ~> (α ~> rhs)))] := is_eval_once.s_call
        simp_all
      contradiction
    contradiction
    cases h_t_lhs
    contradiction
    case arr.comb_call α t_α t_β _ _ _ _ h_t_arr _ _ =>
      cases h_t_arr
      have h_yes_step : is_eval_once SKM[(((M #~>) α) rhs)] SKM[(α ~> (M rhs))] := is_eval_once.arr_call
      simp_all
    contradiction
    case call t_in h_t_rhs' h_t_lhs' =>
      have h := ih₁ h_t_lhs'
      simp_all
      have h := ih₂ h_t_rhs'
      have h_yes_step : is_eval_once SKM[((t_in ~> t₂) rhs)] t₂ := is_eval_once.arr
      simp_all
  cases h_t₂
  contradiction
  case k.comb_call h _ _ =>
    cases h
    contradiction
    case comb_call α _ β _ _ _ _ _ _ _ _ _ h _ _ _ =>
      cases h
      have h_yes_step : is_eval_once SKM[(((M K) α) β)] SKM[(α ~> (β ~> α))] := is_eval_once.k_call
      simp_all
    contradiction
  rfl
  contradiction
  cases h_t₂
  contradiction
  case s.comb_call h _ _ =>
    cases h
    contradiction
    case comb_call α _ β _ γ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ =>
      have h_yes_step : is_eval_once SKM[((((M S) α) β) γ)] SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))] := is_eval_once.s_call
      cases h
      simp_all
      contradiction
      case comb_call h _ _ _ _ =>
        cases h
        simp_all
      contradiction
    contradiction
  rfl
  contradiction
  cases h_t₂
  contradiction
  case arr.comb_call h _ _ =>
    cases h
    contradiction
    case comb_call α _ β _ _ _ _ _ _ _ _ _ h _ _ _ =>
      cases h
      have h_yes_step : is_eval_once SKM[(((M #~>) α) β)] SKM[(α ~> (M β))] := is_eval_once.arr_call
      simp_all
    contradiction
  case arr.arr α t_α₁ β t_β₁ h_t_α₁ h_t_β₁ ih₁ ih₂ α₂ β₂ h_t_α₂ h_t_β₂ =>
    have h := ih₁ h_t_α₁
    simp_all
    rw [ih₂ h_t_β₂]
  contradiction
  case call lhs t_in t_out rhs h_t_lhs h_t_rhs ih₁ ih₂ =>
    cases h_t₂
    contradiction
    case comb_call t_lhs' h_t_lhs' h_t_rhs' h_no_step =>
      have h := ih₁ h_t_lhs'
      rw [← h] at h_no_step
      have h_yes_step : is_eval_once SKM[((t_in ~> t_out) rhs)] t_out := is_eval_once.arr
      simp_all
    repeat contradiction
    case call t_in' h_t_in' h_t_lhs' =>
      have h := ih₁ h_t_lhs'
      have h := ih₁ h_t_lhs
      simp_all

lemma valid_rhs (h_t : valid_judgment SKM[(lhs rhs)] t) : ∃ t_rhs, valid_judgment rhs t_rhs := by
  cases h_t
  repeat (constructor; assumption)

syntax (name := do_stuck_e) "do_stuck_e " : tactic

macro_rules
  | `(tactic| do_stuck_e) =>
    `(tactic| intro ⟨e', h_step⟩; cases h_step; contradiction)

lemma valid_call (h_t : valid_judgment SKM[(lhs rhs)] t) : ∃ t_rhs, valid_judgment rhs t_rhs ∧ (valid_judgment lhs SKM[(t_rhs ~> t)] ∨ ∃ t_lhs, is_typed_comb lhs t_lhs) := by
  cases h_t
  contradiction
  case comb_call t_lhs t_rhs h_t_lhs h_t_rhs no_step =>
    exact ⟨_, ⟨(by assumption), Or.inr ⟨t_lhs, ⟨(by assumption), λ ⟨_, h⟩ => by simp [is_eval_once.no_step no_step] at *⟩⟩⟩⟩
  case k α t_α t_β h_t_α h_t_β =>
    use t_β
    constructor
    assumption
    right
    use SKM[((M K) α)]
    constructor
    apply valid_judgment.comb_call
    apply valid_judgment.comb₀
    apply is_comb.k
    assumption
    repeat do_stuck_e
  case s α t_α β t_β t_γ h_t_α h_t_β h_t_γ =>
    use t_γ
    constructor
    assumption
    right
    use SKM[(((M S) α) β)]
    constructor
    apply valid_judgment.comb_call
    apply valid_judgment.comb_call
    apply valid_judgment.comb₀
    apply is_comb.s
    repeat (assumption; do_stuck_e)
    do_stuck_e
  

end valid_judgment

namespace valid_judgment

@[simp]
lemma weakening : valid_judgment e t → valid_judgment_hard e t := by
  intro h_t
  induction h_t
  apply valid_judgment_hard.comb₀
  assumption
  apply valid_judgment_hard.comb_call
  repeat assumption
  apply valid_judgment_hard.k
  repeat assumption
  apply valid_judgment_hard.s
  repeat assumption
  apply valid_judgment_hard.arr
  repeat assumption
  apply valid_judgment_hard.call
  repeat assumption

theorem preservation (h_t : valid_judgment e t) (h_eval : is_eval_once e e') : valid_judgment e' t := by
  induction h_eval
  

lemma progress (h : valid_judgment e t) : is_value e ∨ ∃ e', is_eval_once e e' := by
  induction h
  exact Or.inl is_value.k
  exact Or.inl is_value.s
  exact Or.inl is_value.m
  exact Or.inl is_value.k₁
  exact Or.inl is_value.s₁
  exact Or.inl is_value.s₂
  exact Or.inl is_value.k₂
  exact Or.inl is_value.s₃
  exact Or.inl is_value.arr
  case call lhs t_in t_out rhs h_t_lhs h_t_rhs ih₁ ih₂ =>
    match ih₁ with
      | .inl h_val_lhs =>
        cases h_val_lhs
        repeat contradiction
        case arr α β =>
          exact Or.inr ⟨β, is_eval_once.arr⟩
        repeat contradiction
        exact Or.inl is_value.k₃
        case k₃ α β x =>
          exact Or.inr ⟨x, is_eval_once.k⟩
        repeat contradiction
        exact Or.inl is_value.s₄
        exact Or.inl is_value.s₅
        case s₅ α β γ x y =>
          exact Or.inr ⟨SKM[((x rhs) (y rhs))], is_eval_once.s⟩
        repeat contradiction
      | .inr ⟨lhs', h_step_lhs⟩ =>
        cases lhs
        repeat contradiction
        right
        case call.h lhs'' rhs' =>
          exact ⟨SKM[(lhs' rhs)], is_eval_once.left (by assumption)⟩
  exact Or.inl is_value.arr₀
  exact Or.inl is_value.arr₁

end valid_judgment


