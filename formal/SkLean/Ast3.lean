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

inductive beta_eq : Expr → Expr → Prop
  | eval  : is_eval_once e₁ e₂ → beta_eq e₁ e₂
  | left  : beta_eq lhs lhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right : beta_eq rhs rhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')]
  | trans : beta_eq e₁ e₂      → beta_eq e₂ e₃ → beta_eq e₁ e₃
  | symm  : beta_eq e₁ e₂      → beta_eq e₂ e₁

inductive is_normal_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e'))                 → is_normal_n 0 e e
  | succ  : is_eval_once e e' → is_normal_n n e' e_final → is_normal_n n.succ e e_final

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
  | arr_call : valid_judgment α t_α
    → valid_judgment β t_β
    → valid_judgment SKM[(α ~> β)] SKM[(α ~> t_β)]
  | k_call   : valid_judgment SKM[((K α) β)]     SKM[(α ~> (β ~> α))]
  | s_call   : valid_judgment SKM[(((S α) β) γ)] SKM[((α ~> (β ~> γ)) ~> ((α ~> β) ~> (α ~> γ)))]
  | call     : valid_judgment lhs SKM[(t_in ~> t_out)]
    → valid_judgment rhs t_in
    → valid_judgment SKM[(lhs rhs)] t_out
  | k₁       : valid_judgment SKM[(K α)]         SKM[((M K) α)]
  | s₁       : valid_judgment SKM[(S α)]         SKM[((M S) α)]
  | s₂       : valid_judgment SKM[((S α) β)]     SKM[(((M S) α) β)]

inductive valid_judgment_hard : Expr → Expr → Prop
  | valid : valid_judgment e t
    → valid_judgment_hard e t
  | step  : is_eval_step t t'
    → valid_judgment_hard e t
    → valid_judgment_hard e t'

@[simp]
lemma m_stuck : is_normal_n 0 SKM[M] SKM[M] := by
  apply is_normal_n.stuck
  intro h
  cases h
  case a.intro h =>
    cases h

@[simp]
lemma k_stuck : is_normal_n 0 SKM[K] SKM[K] := by
  apply is_normal_n.stuck
  intro h
  cases h
  case a.intro h =>
    cases h

@[simp]
lemma s_stuck : is_normal_n 0 SKM[S] SKM[S] := by
  apply is_normal_n.stuck
  intro h
  cases h
  case a.intro h =>
    cases h

namespace beta_eq

@[simp]
lemma go_left : beta_eq lhs lhs' → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)] := by
  apply beta_eq.left

@[simp]
lemma go_right : beta_eq rhs rhs' → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')] := by
  apply beta_eq.right

end beta_eq

namespace valid_judgment

lemma weakening (h : valid_judgment e t) : valid_judgment_hard e t := by
  exact valid_judgment_hard.valid h

lemma preservation (h_t : valid_judgment e t) (h_eval : is_eval_once e e') : valid_judgment_hard e' t := by
  induction h_eval
  case k t_x t_y x y =>
    match h_t with
    | (.call (.call (.k_call) h) _) =>
      exact h.weakening
  case s t_x t_y t_z x y z =>
    match h_t with
      | .call (.call (.call h _) _) _ =>
        cases h
        apply valid_judgment_hard.valid
        apply valid_judgment.call
        apply valid_judgment.call
        case s_call.a.a h_t_y h_t_z ih =>
          apply valid_judgment.call
          exact h_t_y
          exact h_t_z
        case s_call.a.a h =>
          exact h
        case s_call.a.a.a h_t_y h_t_z h_t_x =>
          exact h_t_z
        case call h =>
          cases h
          case call h =>
            cases h
            case call h =>
              cases h
  case arr α β x =>
    cases h_t
    case call t_x h_t_x h =>
      cases h
      case arr_call t_β h_t_β h_t_α =>
        exact h_t_α.weakening
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

end valid_judgment

namespace valid_judgment_hard

theorem preservation (h_pre : valid_judgment_hard e t) (h_step : is_eval_once e e') : valid_judgment_hard e' t := by
  induction h_pre
  case valid e' t' h_t =>
    apply h_t.preservation
    exact h_step
  case step t' t'' e' h_step₁ h_t ih =>
    simp_all
    apply valid_judgment_hard.step
    exact h_step₁
    exact ih

end valid_judgment_hard
