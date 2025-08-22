import Mathlib.Tactic

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | ty   : ℕ    → Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat skmexpr
syntax "K"                     : skmexpr
syntax "S"                     : skmexpr
syntax "M"                     : skmexpr
syntax "Ty" num                : skmexpr
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
  | `(⟪ Ty $n:num ⟫)                   => `(Expr.ty $n)
  | `(⟪ $e:ident ⟫)                    => `($e)
  | `(⟪ # $e:term ⟫)                   => `($e)
  | `(⟪ ($e:skmexpr) ⟫)                => `(⟪$e⟫)
  | `(⟪ ($e₁:skmexpr $e₂:skmexpr) ⟫)   => `(Expr.call ⟪ $e₁ ⟫ ⟪ $e₂ ⟫)

inductive is_eval_once : Expr → Expr → Prop
  | k        : is_eval_once SKM[((((K _t_x) _t_y) x) y)] x
  | s        : is_eval_once SKM[((((((S _t_x) _t_y) _t_z) x) y) z)] SKM[((x z) (y z))]
  | m_k      : is_eval_once SKM[((((((M K) t) _t_y) _x) _y))] t
  | m_s      : is_eval_once SKM[((((((((M S) t_x) t_y) t_z) x) y) z))] SKM[((t_x z) (y z))]
  | m_m_k    : is_eval_once SKM[((M M) K)] SKM[Ty 0]
  | m_m_s    : is_eval_once SKM[((M M) S)] SKM[Ty 0]
  | m_m_m    : is_eval_once SKM[((M M) M)] SKM[Ty 0]
  | m_call   : is_eval_once SKM[(M (lhs rhs))] SKM[((M lhs) rhs)]

inductive is_eval_step : Expr → Expr → Prop
  | left : is_eval_step lhs lhs'
    → is_eval_step SKM[(lhs rhs)] SKM[(lhs' rhs)]
  | step : is_eval_once e e'
    → is_eval_step e e'

inductive beta_eq : Expr → Expr → Prop
  | rfl   : beta_eq e e
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

inductive Typ where
  | raw   : Expr → Typ
  | arrow : Typ  → Typ → Typ

infix:20 "~>" => Typ.arrow

inductive valid_judgment : Expr → Typ → Prop
  | k      : valid_judgment SKM[K]             (.raw SKM[(M K)])
  | s      : valid_judgment SKM[S]             (.raw SKM[(M S)])
  | m      : valid_judgment SKM[M]             (.raw SKM[(M M)])
  | k_call : valid_judgment SKM[((K α) β)]     ((.raw α) ~> ((.raw β) ~> (.raw α)))
  | s_call : valid_judgment SKM[(((S α) β) γ)] ((((.raw α) ~> ((.raw β) ~> (.raw γ)))
           ~> ((.raw α) ~> (.raw β)))
           ~> (.raw γ))
  | call   : valid_judgment lhs (t_in ~> t_out)
    → valid_judgment rhs t_in
    → valid_judgment SKM[(lhs rhs)] t_out
  | k₁     : valid_judgment SKM[(K α)]         (.raw SKM[((M K) α)])
  | s₁     : valid_judgment SKM[(S α)]         (.raw SKM[((M S) α)])
  | s₂     : valid_judgment SKM[((S α) β)]     (.raw SKM[(((M S) α) β)])

inductive valid_judgment_hard : Expr → Typ → Prop
  | k      : valid_judgment_hard SKM[K]             (.raw SKM[(M K)])
  | s      : valid_judgment_hard SKM[S]             (.raw SKM[(M S)])
  | m      : valid_judgment_hard SKM[M]             (.raw SKM[(M M)])
  | k_call : valid_judgment_hard SKM[((K α) β)]     ((.raw α) ~> ((.raw β) ~> (.raw α)))
  | s_call : valid_judgment_hard SKM[(((S α) β) γ)] ((((.raw α) ~> ((.raw β) ~> (.raw γ)))
           ~> ((.raw α) ~> (.raw β)))
           ~> (.raw γ))
  | call   : valid_judgment_hard lhs (t_in ~> t_out)
    → valid_judgment_hard rhs t_in
    → valid_judgment_hard SKM[(lhs rhs)] t_out
  | k₁     : valid_judgment_hard SKM[(K α)]         (.raw SKM[((M K) α)])
  | s₁     : valid_judgment_hard SKM[(S α)]         (.raw SKM[((M S) α)])
  | s₂     : valid_judgment_hard SKM[((S α) β)]     (.raw SKM[(((M S) α) β)])
  | beq  : valid_judgment_hard e (.raw t)
    → beta_eq t t'
    → valid_judgment_hard e (.raw t')

lemma normal_beta_eq : is_normal_n n e e_final → beta_eq e e_final := by
  intro h
  induction h
  apply beta_eq.rfl
  case succ e e' n e_final h_eval h_norm h_eq =>
    apply beta_eq.symm
    apply beta_eq.trans
    exact beta_eq.symm h_eq
    apply beta_eq.symm
    exact beta_eq.eval h_eval

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
lemma m_distributes : beta_eq SKM[(M (lhs rhs))] SKM[((M lhs) rhs)] := by
  apply beta_eq.trans
  apply beta_eq.eval
  apply is_eval_once.m_call
  exact beta_eq.rfl

@[simp]
lemma go_left : beta_eq lhs lhs' → beta_eq SKM[(lhs rhs)] SKM[(lhs' rhs)] := by
  apply beta_eq.left

@[simp]
lemma go_right : beta_eq rhs rhs' → beta_eq SKM[(lhs rhs)] SKM[(lhs rhs')] := by
  apply beta_eq.right

end beta_eq

namespace valid_judgment

lemma weakening : valid_judgment e t → valid_judgment_hard e t := by
  intro h
  induction h
  apply valid_judgment_hard.k
  apply valid_judgment_hard.s
  apply valid_judgment_hard.m
  apply valid_judgment_hard.k_call
  apply valid_judgment_hard.s_call
  apply valid_judgment_hard.call
  case call.a ih _ =>
    exact ih
  case call.a ih =>
    exact ih
  apply valid_judgment_hard.k₁
  apply valid_judgment_hard.s₁
  apply valid_judgment_hard.s₂

lemma preservation (h_t : valid_judgment e t) (h_eval : is_eval_once e e') : valid_judgment_hard e' t := by
  induction h_eval
  cases h_t
  case k.call h_t_in h =>
    cases h
    case call h_t_x h =>
      cases h
      exact h_t_x.weakening
      case call h h_k₁ =>
        cases h_k₁
        case call h =>
          cases h
  cases h_t
  case s.call h =>
    match h with
      | .call (.call (.call (.call (.call h _) _) _) _) _ =>
        cases h
  cases h_t
  case m_k.call h =>
    match h with
      | .call (.call (.call (.call h _) _) _) _ =>
        cases h
  cases h_t
  case m_s.call h =>
    match h with
      | .call (.call (.call (.call (.call (.call h _) _) _) _) _) _ =>
        cases h
  cases h_t
  case m_m_k.call h =>
    cases h
    case call h =>
      cases h
  cases h_t
  case m_m_s.call h =>
    cases h
    case call h =>
      cases h
  cases h_t
  case m_m_m.call h =>
    cases h
    case call h =>
      cases h
  case m_call lhs rhs =>
    cases h_t
    case call h =>
      cases h

end valid_judgment
