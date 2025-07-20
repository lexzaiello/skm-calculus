import Mathlib.Tactic

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | call : Expr → Expr → Expr

declare_syntax_cat skmexpr
syntax "K"                                                             : skmexpr
syntax "S"                                                             : skmexpr
syntax "M"                                                             : skmexpr
syntax "(" skmexpr skmexpr ")" : skmexpr
syntax ident                                                           : skmexpr
syntax "#" term                                                        : skmexpr
syntax "(" skmexpr ")"                                                 : skmexpr

syntax " ⟪ " skmexpr " ⟫ "                                             : term
syntax "SKM[ " skmexpr " ] "                                           : term

macro_rules
  | `(SKM[ $e:skmexpr ]) => `(⟪ $e ⟫)

macro_rules
  | `(⟪ K ⟫)                           => `(Expr.k)
  | `(⟪ S ⟫)                           => `(Expr.s)
  | `(⟪ M ⟫)                           => `(Expr.m)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)   => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

-- M (K α β x y) = ((M (K α β x)) y)
-- M K = K Type Type
-- M : S K M
-- M e : S K M e
-- K : S (K) (K M)
-- K α β : (S (K M) K α β = M (K α) β

def id_e : Expr := SKM[((S K) K)]

inductive is_eval_once : Expr → Expr → Prop
  | k      : is_eval_once SKM[((K x) _y)] x
  | s      : is_eval_once SKM[(((S x) y) z)] SKM[((x z) (y z))]
  | m_call : is_eval_once SKM[(M (lhs rhs))] SKM[((M lhs) rhs)]
  | m_m    : is_eval_once SKM[(M M)] SKM[((S (K M)) M)]
  | m_k    : is_eval_once SKM[(M K)] SKM[((S (K M)) K)]
  | m_s    : is_eval_once SKM[(M S)] SKM[((S (K M)) S)]

inductive beta_eq : Expr → Expr → Prop
  | rfl   : beta_eq e e
  | eval  : is_eval_once e₁ e₂ → beta_eq e₁ e₂
  | left  : beta_eq lhs lhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | right : beta_eq rhs rhs'   → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')]
  | trans : beta_eq e₁ e₂      → beta_eq e₂ e₃ → beta_eq e₁ e₃
  | symm  : beta_eq e₁ e₂      → beta_eq e₂ e₁

inductive valid_judgment : Expr → Expr → Prop
  | call : valid_judgment lhs t_f
    → is_eval_once SKM[(t_f rhs)] t'
    → valid_judgment SKM[(lhs rhs)] t'
  | s : valid_judgment SKM[S] SKM[(M S)]
  | k : valid_judgment SKM[K] SKM[(M K)]
  | m : valid_judgment SKM[M] SKM[(M M)]

inductive valid_judgment_hard : Expr → Expr → Prop
  | call    : valid_judgment_hard lhs t_f
    → beta_eq SKM[(t_f rhs)] t'
    → valid_judgment_hard SKM[(lhs rhs)] t'
  | s       : valid_judgment_hard SKM[S] SKM[(M S)]
  | k       : valid_judgment_hard SKM[K] SKM[(M K)]
  | m       : valid_judgment_hard SKM[M] SKM[(M M)]
  | beta_eq : valid_judgment_hard e t₁
    → beta_eq t₁ t₂
    → valid_judgment_hard e t₂

namespace valid_judgment

lemma imp_m : valid_judgment e t → beta_eq SKM[(M e)] t := by
  intro h_t
  induction h_t
  case call lhs t_f rhs t' h_t_f h_eval ih =>
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m_call
    apply beta_eq.trans
    apply beta_eq.left
    exact ih
    exact beta_eq.eval h_eval
  repeat exact beta_eq.rfl

lemma weakening : valid_judgment e t → valid_judgment_hard e t := by
  intro h
  induction h
  apply valid_judgment_hard.call
  case call.a h =>
    exact h
  case call.a h _ =>
    exact beta_eq.eval h
  apply valid_judgment_hard.s
  apply valid_judgment_hard.k
  apply valid_judgment_hard.m

end valid_judgment

lemma preservation_k_reverse : valid_judgment x α → valid_judgment_hard SKM[((K x) y)] α := by
  intro h_t
  apply valid_judgment_hard.beta_eq
  apply valid_judgment_hard.call
  apply valid_judgment_hard.call
  apply valid_judgment_hard.k
  apply beta_eq.symm
  apply beta_eq.eval
  apply is_eval_once.m_call
  apply beta_eq.symm
  apply beta_eq.eval
  apply is_eval_once.m_call
  apply beta_eq.trans
  apply beta_eq.right
  apply beta_eq.eval
  apply is_eval_once.k
  exact h_t.imp_m

lemma preservation : valid_judgment e t → is_eval_once e e' → valid_judgment e' t := by
  intro h_t h_eval
  induction e
  cases h_eval
  cases h_eval
  cases h_eval
  case call lhs rhs ih₁ ih₂ =>
    cases h_eval
    cases h_t
    case k.call t_f h_t_f h_eval =>
      cases h_t_f
      case call h _ =>
        cases h
        case k h =>
          cases h
    cases h_t
    case s.call t_f h_t_f h_eval =>
      cases h_t_f
      case call h _ =>
        cases h
        case call h _ =>
          cases h
          case s h =>
            cases h
    cases h_t
    case m_call.call t_f h_t_f h_eval =>
      cases h_t_f
      case m =>
        cases h_eval
    cases h_t
    case m_m.call h _ =>
      cases h
      case m h =>
        cases h
    cases h_t
    case m_k.call h _ =>
      cases h
      case m h =>
        cases h
    cases h_t
    case m_s.call h _ =>
      cases h
      case m h =>
        cases h
