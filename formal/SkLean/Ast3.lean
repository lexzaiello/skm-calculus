import Mathlib.Tactic

inductive Expr where
  | k    : Expr
  | s    : Expr
  | m    : Expr
  | call : Expr → Expr → Expr
deriving BEq, Repr

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

inductive is_eval_once : Expr → Expr → Prop
  | k        : is_eval_once SKM[((((K _t_x) x) _t_y) _y)] x
  | s        : is_eval_once SKM[((((((S _t_x) x) _t_y) y) _t_z) z)] SKM[((x z) (y z))]
  | m_k      : is_eval_once SKM[((((((M K) t) _x) _t_y) _y))] t
  | m_s      : is_eval_once SKM[((((((((M S) t_x) x) t_y) y) t_z) z))] SKM[((t_x z) (y z))]
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

inductive is_out : Expr → Expr → Prop
  | k    : is_out SKM[(K t)] t
  | s    : is_out SKM[(((((S t_x) x) t_y) y) t_z)] SKM[((t_x z) (y z))]
  | call : is_out lhs t_out
    → is_out SKM[(lhs rhs)] t_out

inductive is_in : Expr → Expr → Prop
  | k  : is_in SKM[K] any
  | s  : is_in SKM[S] any
  | m  : is_in SKM[M] any
  | k₁ : is_in SKM[(K t)] t
  | k₂ : is_in SKM[((K t) e)] any
  | k₃ : is_in SKM[(((K t_x) x) t_y)] t_y
  | s₁ : is_in SKM[(S t)] t
  | s₂ : is_in x t_z
    → is_in SKM[((S t_x) x)] any
  | s₃ : is_in x t_z
    → is_in y t_z
    → is_in SKM[(((S t_x) x) t_y)] t_y
  | s₄ : is_in x t_z
    → is_in y t_z
    → is_in SKM[((((S t_x) x) t_y) y)] any
  | s₅ : is_in x t_z
    → is_in y t_z
    → is_in SKM[(((((S t_x) x) t_y) y) t_z)] t_z
  | call : is_in lhs t_in
    → is_out lhs t_out
    → is_in t_out t
    → is_in SKM[(lhs rhs)] t

inductive valid_judgment : Expr → Expr → Prop
  | k    : valid_judgment SKM[K] SKM[(M K)]
  | s    : valid_judgment SKM[S] SKM[(M S)]
  | m    : valid_judgment SKM[M] SKM[(M M)]
  | call  : is_in lhs t_rhs
    → valid_judgment lhs t_lhs
    → valid_judgment rhs t_rhs
    → is_out lhs t_out
    → valid_judgment SKM[(lhs rhs)] t_out

inductive valid_judgment_hard : Expr → Expr → Prop
  | k    : valid_judgment_hard SKM[K] SKM[(M K)]
  | s    : valid_judgment_hard SKM[S] SKM[(M S)]
  | m    : valid_judgment_hard SKM[M] SKM[(M M)]
  | call : is_in lhs t_rhs
    → valid_judgment_hard lhs t_lhs
    → valid_judgment_hard rhs t_rhs
    → is_out lhs t_out
    → valid_judgment_hard SKM[(lhs rhs)] t_out
  | beq  : valid_judgment_hard e t
    → beta_eq t t'
    → valid_judgment_hard e t'

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
  case call lhs rhs t_lhs t_rhs t_out h_in h_t_lhs h_t_rhs h_out h_t_lhs' h_t_rhs' =>
    apply valid_judgment_hard.call
    exact h_in
    exact h_t_lhs'
    exact h_t_rhs'
    exact h_out

lemma t_k_x (h : valid_judgment SKM[((((K t_x) x) _t_y) y)] t_x) : valid_judgment_hard x t_x := by
  cases h
  case call t_rhs t_lhs h_in h_t_lhs h_t_rhs h_out =>
    cases h_t_lhs
    case call t_rhs' t_lhs' h_in' h_t_lhs' h_t_rhs' h_out' =>
      cases h_t_lhs'
      case call t_rhs'' t_lhs'' h_in'' h_t_lhs'' h_t_rhs'' h_out'' =>
        cases h_t_lhs''
        case call t_rhs''' t_lhs''' h_in''' h_t_lhs''' h_t_rhs''' h_out''' =>
          cases h_out''
          cases h_in''
          cases h_in'''
          cases h_t_lhs'''
          exact h_t_rhs''.weakening
          case k.call h_in'''' h_out'''' =>
            cases h_out''''
            repeat cases h_in''''
          case call h =>
            cases h

lemma preservation (h_t : valid_judgment e t) (h_eval : is_eval_once e e') : valid_judgment_hard e' t := by
  cases h_eval
  

end valid_judgment
