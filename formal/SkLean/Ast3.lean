import Mathlib.Tactic

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | ty   : Expr
  | arr  : Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat skmexpr
syntax "K"                     : skmexpr
syntax "S"                     : skmexpr
syntax "M"                     : skmexpr
syntax "#~>"                   : skmexpr
syntax skmexpr "~>" skmexpr    : skmexpr
syntax "Ty"                    : skmexpr
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
  | `(⟪ Ty ⟫)                          => `(Expr.ty)
  | `(⟪ #~> ⟫)                         => `(Expr.arr)
  | `(⟪ $e₁:skmexpr ~> $e₂:skmexpr ⟫)  => `(Expr.call (Expr.call Expr.arr ⟪ $e₁ ⟫) ⟪ $e₂ ⟫)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)   => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

inductive is_eval_once : Expr → Expr → Prop
  | k        : is_eval_once SKM[((((K _t_x) _t_y) x) y)] x
  | s        : is_eval_once SKM[((((((S _t_x) _t_y) _t_z) x) y) z)] SKM[((x z) (y z))]
  | arr      : is_eval_once SKM[((α ~> β) x)] β
  | k_call   : is_eval_once SKM[(((M K) α) β)] SKM[(α ~> (β ~> α))]
  | s_call   : is_eval_once SKM[((((M S) α) β) γ)] SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> γ))]
  | m_call   : is_eval_once SKM[(M (lhs rhs))] SKM[((M lhs) rhs)]

inductive is_eval_step : Expr → Expr → Prop
  | left : is_eval_step lhs lhs'
    → is_eval_step SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | step : is_eval_once e e'
    → is_eval_step e e'

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
  | k    : is_value SKM[K]
  | s    : is_value SKM[S]
  | m    : is_value SKM[M]
  | arr  : is_value SKM[(α ~> β)]
  | arr₁ : is_value SKM[(#~> α)]
  | arr₀ : is_value SKM[(#~>)]
  | k₁   : is_value SKM[(K α)]
  | k₂   : is_value SKM[((K α) β)]
  | k₃   : is_value SKM[(((K α) β) x)]
  | s₁   : is_value SKM[(S α)]
  | s₂   : is_value SKM[((S α) β)]
  | s₃   : is_value SKM[(((S α) β) γ)]
  | s₄   : is_value SKM[((((S α) β) γ) x)]
  | s₅   : is_value SKM[(((((S α) β) γ) x) y)]

inductive is_value_n : ℕ → Expr → Expr → Prop
  | value : is_value e        → is_value_n 0 e e
  | succ  : is_eval_step e e' → is_value_n n e' e_final → is_value_n n.succ e e_final

def is_normal (e : Expr) :=¬(∃ e', is_eval_once e e')

def subtree_is_in (e in_e : Expr) : Prop :=
  e == in_e ∨
    match in_e with
      | SKM[(lhs rhs)] => subtree_is_in e lhs ∨ subtree_is_in e rhs
      | _ => false

inductive valid_judgment : Expr → Expr → Prop
  | k        : valid_judgment SKM[K]             SKM[(M K)]
  | s        : valid_judgment SKM[S]             SKM[(M S)]
  | m        : valid_judgment SKM[M]             SKM[(M M)]
  | arr₀     : valid_judgment SKM[#~>]           SKM[(Ty ~> (Ty ~> Ty))]
  | k_call   : valid_judgment α t_α
    → valid_judgment β t_β
    → valid_judgment SKM[((K α) β)]     SKM[(α ~> (β ~> α))]
  | s_call   : valid_judgment α t_α
    → valid_judgment β t_β
    → valid_judgment γ t_γ
    → valid_judgment SKM[(((S α) β) γ)] SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | call     : valid_judgment lhs SKM[(t_in ~> t_out)]
    → valid_judgment rhs t_in
    → valid_judgment SKM[(lhs rhs)] t_out
  | k₁       : valid_judgment α t_α
    → valid_judgment SKM[(K α)]         SKM[((M K) α)]
  | s₁       : valid_judgment α t_α
    → valid_judgment SKM[(S α)]         SKM[((M S) α)]
  | s₂       : valid_judgment α t_α
    → valid_judgment β t_β
    → valid_judgment SKM[((S α) β)]     SKM[(((M S) α) β)]

inductive valid_judgment_hard : Expr → Expr → Prop
  | k        : valid_judgment_hard SKM[K]             SKM[(M K)]
  | s        : valid_judgment_hard SKM[S]             SKM[(M S)]
  | m        : valid_judgment_hard SKM[M]             SKM[(M M)]
  | arr₀     : valid_judgment_hard SKM[#~>]           SKM[(Ty ~> (Ty ~> Ty))]
  | k_call   : valid_judgment_hard α t_α
    → valid_judgment_hard β t_β
    → valid_judgment_hard SKM[((K α) β)] SKM[(α ~> (β ~> α))]
  | s_call   : valid_judgment_hard α t_α
    → valid_judgment_hard β t_β
    → valid_judgment_hard γ t_γ
    → valid_judgment_hard SKM[(((S α) β) γ)] SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | call     : valid_judgment_hard lhs SKM[(t_in ~> t_out)]
    → valid_judgment_hard rhs t_in
    → valid_judgment_hard SKM[(lhs rhs)] t_out
  | k₁       : valid_judgment_hard α t_α
    → valid_judgment_hard SKM[(K α)] SKM[((M K) α)]
  | s₁       : valid_judgment_hard α t_α
    → valid_judgment_hard SKM[(S α)] SKM[((M S) α)]
  | s₂       : valid_judgment_hard α t_α
    → valid_judgment_hard β t_β
    → valid_judgment_hard SKM[((S α) β)]     SKM[(((M S) α) β)]
  | step  : beta_eq t t'
    → valid_judgment_hard e t
    → valid_judgment_hard e t'

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

lemma imp_beta_eq : is_eval_step e e' → beta_eq e e' := by
  intro h_step
  induction h_step
  case step lhs lhs' rhs =>
    exact beta_eq.eval rhs
  case left lhs lhs' rhs h_step h_beq =>
    apply beta_eq.trans
    apply beta_eq.left
    exact h_beq
    exact beta_eq.rfl

end is_eval_step

namespace is_eval_once

lemma same_eval_eq : is_eval_once e e₁ → is_eval_once e e₂ → e₁ = e₂ := by
  intro h_step₁ h_step₂
  induction h_step₁
  repeat (cases h_step₂; rfl)

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

@[simp]
lemma no_step (h : is_value e) : ¬ ∃ e', is_eval_step e e' := by
  cases h
  repeat (intro ⟨e', h⟩; match h with | .step h => cases h)

lemma value_lhs (h : is_value SKM[(lhs rhs)]) : is_value lhs := by
  cases h
  apply is_value.arr₁
  apply is_value.arr₀
  apply is_value.k
  apply is_value.k₁
  apply is_value.k₂
  apply is_value.s
  apply is_value.s₁
  apply is_value.s₂
  apply is_value.s₃
  apply is_value.s₄

end is_value

namespace valid_judgment

lemma weakening (h : valid_judgment e t) : valid_judgment_hard e t := by
  induction h
  apply valid_judgment_hard.k
  apply valid_judgment_hard.s
  apply valid_judgment_hard.m
  apply valid_judgment_hard.arr₀
  apply valid_judgment_hard.k_call
  assumption
  assumption
  apply valid_judgment_hard.s_call
  case call lhs t_in t_out rhs h_T_lhs h_t_rhs ih₁ ih₂ =>
    apply valid_judgment_hard.call
    exact ih₁
    exact ih₂
  assumption
  assumption
  assumption
  apply valid_judgment_hard.k₁
  assumption
  apply valid_judgment_hard.s₁
  assumption
  apply valid_judgment_hard.s₂
  assumption
  assumption

lemma preservation (h_t : valid_judgment e t) (h_eval : is_eval_once e e') : valid_judgment_hard e' t := by
  induction h_eval
  case k t_x t_y x y =>
    match h_t with
    | (.call (.call (.k_call h_t_α h_t_β) h) _) =>
      exact h.weakening
  case s t_x t_y t_z x y z =>
    match h_t with
      | .call (.call (.call h _) _) _ =>
        cases h
        apply valid_judgment_hard.call
        apply valid_judgment_hard.call
        case s_call.a.a h_t_y h_t_z ih =>
          exact ih.weakening
        case s_call.a.a h _ =>
          apply valid_judgment.weakening
          assumption
        apply valid_judgment_hard.call
        case s_call.a h_t_y h_t_z h_t_x =>
          apply valid_judgment.weakening
          assumption
        case call h =>
          cases h
          case call h =>
            cases h
            case call h =>
              cases h
        case s_call.a.a h _ =>
          apply valid_judgment.weakening
          assumption
  case arr α β x =>
    cases h_t
    case call t_x h_t_x h =>
      cases h
      case call h =>
        cases h
        case call h =>
          cases h
  case k_call α β =>
    match h_t with
      | (.call (.call (.call h _) _) _) =>
      cases h
  case s_call α β =>
    match h_t with
      | (.call (.call (.call (.call h _) _) _) _) =>
      cases h
  case m_call lhs rhs =>
    match h_t with
      | (.call h _) =>
        cases h

lemma progress (h : valid_judgment e t) : is_value e ∨ ∃ e', is_eval_step e e' := by
  induction h
  left
  exact is_value.k
  left
  exact is_value.s
  left
  exact is_value.m
  left
  apply is_value.arr₀
  left
  apply is_value.k₂
  left
  apply is_value.s₃
  case call lhs t_in t_out rhs h_t_lhs h_t_rhs ih₁ ih₂ =>
    cases ih₁
    case inl h =>
      cases h
      left
      exact is_value.k₁
      left
      exact is_value.s₁
      cases h_t_lhs
      right
      case arr.h α β =>
        use β
        apply is_eval_step.step
        apply is_eval_once.arr
      left
      exact is_value.arr
      left
      exact is_value.arr₁
      left
      exact is_value.k₂
      left
      exact is_value.k₃
      right
      case k₃.h α β x =>
        use x
        apply is_eval_step.step
        exact is_eval_once.k
      left
      exact is_value.s₂
      left
      exact is_value.s₃
      left
      exact is_value.s₄
      left
      exact is_value.s₅
      case s₅ α β γ x y =>
        right
        use SKM[((x rhs) (y rhs))]
        apply is_eval_step.step
        exact is_eval_once.s
    case inr h =>
      obtain ⟨e', h⟩ := h
      right
      use SKM[(e' rhs)]
      apply is_eval_step.left
      exact h
  left
  apply is_value.k₁
  left
  apply is_value.s₁
  left
  apply is_value.s₂

lemma preservation' (h_t : valid_judgment e t) (h_step : is_eval_step_once e e') : valid_judgment_hard e' t := by
  induction h_step generalizing t
  case left lhs lhs' rhs' ih =>
    cases ih
    cases h_t
    case k.call h =>
      cases h
      case call h =>
        cases h
        case call h =>
          cases h
          apply valid_judgment_hard.call
          case k_call.a h =>
            exact h.weakening
          case k_call.a h _ _ =>
            apply weakening
            assumption
          contradiction
    cases h_t
    case s.call h =>
      cases h
      case call h =>
        cases h
        case call h =>
          cases h
          case call h =>
            cases h
            apply valid_judgment_hard.call
            case s_call.a h h_t_y h_t_z =>
              apply valid_judgment_hard.call
              apply valid_judgment_hard.call
              exact h_t_z.weakening
              apply weakening
              assumption
              apply valid_judgment_hard.call
              apply weakening
              assumption
              apply weakening
              assumption
            case s_call.a h _ _ _ =>
              apply weakening
              assumption
            contradiction
    cases h_t
    case arr.call h =>
      cases h
      case call h =>
        cases h
        apply valid_judgment_hard.call
        contradiction
        case call.a α x t_in h_t_rhs t_in h_t_x t' h_t_lhs' =>
          apply weakening
          assumption
    repeat contradiction
  case step e' e'' h_eval =>
    apply valid_judgment.preservation
    exact h_t
    exact h_eval

end valid_judgment

namespace valid_judgment_hard

lemma valid_lhs (h : valid_judgment_hard SKM[(lhs rhs)] t) : ∃ t_in t_out, valid_judgment_hard lhs SKM[(t_in ~> t_out)] := by
  cases h
  case call t_in' h_t_ih h_t_lhs =>
    use t_in'
    use t
  

theorem preservation (h_pre : valid_judgment_hard e t) (h_step : is_eval_once e e') : valid_judgment_hard e' t := by
  induction h_pre generalizing e'
  contradiction
  contradiction
  contradiction
  contradiction
  contradiction
  contradiction
  contradiction
  contradiction
  case call lhs t_in t_out rhs h_t_lhs h_t_in ih₁ ih₂ =>
    have h_t_e' : valid_judgment_hard SKM[(lhs rhs)] SKM[((t_in ~>t_out) rhs)] := by
      apply valid_judgment_hard.step
      apply beta_eq.eval
      apply is_eval_once.arr
      use t_in
      use rhs
      apply valid_judgment_hard.step
      apply beta_eq.symm
      apply beta_eq.eval
      apply is_eval_once.arr
      apply valid_judgment_hard.step
      apply beta_eq.symm
      apply beta_eq.eval
      apply is_eval_once.arr
      apply valid_judgment_hard.call
      exact h_t_lhs
      exact h_t_in
    apply valid_judgment_hard.step
    apply beta_eq.eval
    apply is_eval_once.arr
    use t_in
    use rhs
    cases h_step
    
    sorry

theorem progress (h_t : valid_judgment_hard e t) : is_value e ∨ ∃ e', is_eval_step e e' := by
  induction h_t
  case valid e' t' h =>
    exact h.progress
  case step t' t'' e' h_step h_t ih =>
    exact ih

theorem progress_hard (h_t : valid_judgment_hard e t) : ∃ n e_final, is_value_n n e e_final := by
  induction h_t
  case valid e' t' h_t =>
    have h := h_t.progress
    match h with
      | .inl h =>
        use 0
        use e'
        apply is_value_n.value
        exact h
      | .inr ⟨e'₁, h⟩ =>
        induction h generalizing t'
        case left lhs lhs' rhs h_step_lhs ih =>
          have ⟨t_lhs, h_t_lhs⟩ := h_t.valid_lhs
          have ⟨n_lhs, lhs_final, h_final_lhs⟩ := ih h_t_lhs h_t_lhs.progress
          have h_t' : ∃ t, valid_judgment SKM[(lhs_final rhs)] t := by
            use sorry
            apply valid_judgment.call
            
            sorry
        sorry

end valid_judgment_hard

