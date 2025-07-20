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
  | call : valid_judgment lhs t_lhs
    → valid_judgment SKM[(t_lhs rhs)] t_t_call
    → is_eval_once SKM[(t_lhs rhs)] t'
    → valid_judgment SKM[(lhs rhs)] SKM[((M lhs) rhs)]
  | s : valid_judgment SKM[S] SKM[((S (K M)) S)]
  | k : valid_judgment SKM[K] SKM[((S (K M)) K)]
  | m : valid_judgment SKM[M] SKM[((S (K M)) M)]

inductive valid_judgment_hard : Expr → Expr → Prop
  | call : valid_judgment_hard lhs t_lhs
    → beta_eq SKM[(t_lhs rhs)] t'
    → valid_judgment_hard SKM[(lhs rhs)] t'
  | s : valid_judgment_hard SKM[S] SKM[((S (K M)) S)]
  | k : valid_judgment_hard SKM[K] SKM[((S (K M)) K)]
  | m : valid_judgment_hard SKM[M] SKM[((S (K M)) M)]
  | beta_eq : valid_judgment_hard e t₁
    → beta_eq t₁ t₂
    → valid_judgment_hard e t₂

inductive is_normal_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e'))                 → is_normal_n 0 e e
  | succ  : is_eval_once e e' → is_normal_n n e' e_final → is_normal_n n.succ e e_final

namespace valid_judgment_hard

lemma imp_m_eval : valid_judgment_hard e t → _root_.beta_eq SKM[(M e)] t := by
  intro h_t
  induction h_t
  case call lhs t_lhs rhs t' h_t_lhs h_eval ih₁ =>
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m_call
    apply beta_eq.trans
    apply beta_eq.left
    exact ih₁
    exact h_eval
  apply _root_.beta_eq.trans
  apply _root_.beta_eq.eval
  apply is_eval_once.m_s
  apply _root_.beta_eq.rfl
  apply _root_.beta_eq.trans
  apply _root_.beta_eq.eval
  apply is_eval_once.m_k
  apply _root_.beta_eq.rfl
  apply _root_.beta_eq.trans
  apply _root_.beta_eq.eval
  apply is_eval_once.m_m
  apply _root_.beta_eq.rfl
  apply _root_.beta_eq.trans
  case beta_eq.a ih =>
    exact ih
  case beta_eq.a h _ =>
    exact h

end valid_judgment_hard

namespace valid_judgment

lemma imp_m_eval : valid_judgment e t → beta_eq SKM[(M e)] t := by
  intro h_t
  induction h_t
  case call lhs t_lhs rhs t_t_call t' h_t_lhs h_t_t_call h_eval ih₁ ih₂=>
    apply beta_eq.eval
    apply is_eval_once.m_call
  apply beta_eq.eval
  apply is_eval_once.m_s
  apply beta_eq.eval
  apply is_eval_once.m_k
  apply beta_eq.eval
  apply is_eval_once.m_m

lemma imp_m_eval_once : valid_judgment e t → is_eval_once SKM[(M e)] t := by
  intro h_t
  induction h_t
  case call lhs t_lhs rhs t_t_call t' h_t_lhs h_t_t_call h_eval ih₁ ih₂=>
    apply is_eval_once.m_call
  apply is_eval_once.m_s
  apply is_eval_once.m_k
  apply is_eval_once.m_m

lemma weakening : valid_judgment e t → valid_judgment_hard e t := by
  intro h
  induction h
  apply valid_judgment_hard.call
  case call.a h _ =>
    exact h
  case call.a h _ _ =>
    exact beta_eq.eval h
  apply valid_judgment_hard.s
  apply valid_judgment_hard.k
  apply valid_judgment_hard.m

end valid_judgment

namespace beta_eq

@[simp]
lemma m_distributes : beta_eq SKM[((M lhs) rhs)] SKM[(M (lhs rhs))] := by
  apply beta_eq.symm
  apply beta_eq.eval
  apply is_eval_once.m_call

end beta_eq

lemma preservation_k : valid_judgment SKM[((K x) y)] α → valid_judgment x α := by
  intro h_t
  cases h_t
  case call t_lhs t_t_call t' h_t_lhs h_t_call h_eval =>
    cases h_t_lhs
    case call t_lhs t_t_call t' h_t_lhs h_t_call h_eval_t' =>
      cases h_t_lhs
      case k t_t_call' t'' h_t_call' =>
        cases h_eval_t'
        cases h_eval

lemma preservation_s : valid_judgment SKM[(((S x) y) z)] α → valid_judgment SKM[((x z) (y z))] α := by
  intro h_t
  cases h_t
  case call t_lhs t_t_call t' h_t_lhs h_t_call h_eval =>
    cases h_t_lhs
    case call t_lhs t_t_call t' h_t_lhs h_t_call h_eval_t' =>
      cases h_t_lhs
      case call t_t_call' t'' h_t_call' =>
        cases h_eval_t'

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

lemma m_stuck : is_normal_n 0 SKM[M] SKM[M] := by
  apply is_normal_n.stuck
  intro h
  cases h
  case a.intro h =>
    cases h

lemma k_stuck : is_normal_n 0 SKM[K] SKM[K] := by
  apply is_normal_n.stuck
  intro h
  cases h
  case a.intro h =>
    cases h

lemma s_stuck : is_normal_n 0 SKM[S] SKM[S] := by
  apply is_normal_n.stuck
  intro h
  cases h
  case a.intro h =>
    cases h

lemma preservation : valid_judgment e t → is_eval_once e e' → valid_judgment_hard e' t := by
  intro h_t h_eval
  cases h_eval
  apply valid_judgment.weakening
  apply preservation_k
  exact h_t
  apply valid_judgment.weakening
  apply preservation_s
  exact h_t
  apply valid_judgment_hard.beta_eq
  apply valid_judgment_hard.call
  apply valid_judgment_hard.call
  apply valid_judgment_hard.m
  apply beta_eq.eval
  apply is_eval_once.s
  apply beta_eq.left
  apply beta_eq.left
  apply beta_eq.eval
  apply is_eval_once.k
  apply beta_eq.trans
  apply beta_eq.m_distributes
  apply beta_eq.trans
  apply beta_eq.right
  apply beta_eq.m_distributes
  apply valid_judgment.imp_m_eval
  exact h_t
  apply valid_judgment_hard.beta_eq
  apply valid_judgment_hard.call
  apply valid_judgment_hard.call
  apply valid_judgment_hard.s
  apply beta_eq.eval
  apply is_eval_once.s
  apply beta_eq.left
  apply beta_eq.left
  apply beta_eq.eval
  apply is_eval_once.k
  apply beta_eq.trans
  apply beta_eq.m_distributes
  apply beta_eq.trans
  apply beta_eq.rfl
  cases h_t
  case m_m.a.a.a.call t_lhs t_t_call t' h_t_lhs h_t_call h_eval =>
    apply beta_eq.symm
    apply beta_eq.trans
    apply beta_eq.left
    apply beta_eq.eval
    apply is_eval_once.m_m
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.s
    apply beta_eq.trans
    apply beta_eq.left
    apply beta_eq.eval
    apply is_eval_once.k
    apply beta_eq.trans
    apply beta_eq.right
    apply beta_eq.eval
    apply is_eval_once.m_m
    apply beta_eq.rfl
  apply valid_judgment_hard.beta_eq
  apply valid_judgment_hard.call
  apply valid_judgment_hard.call
  apply valid_judgment_hard.s
  apply beta_eq.eval
  apply is_eval_once.s
  apply beta_eq.left
  apply beta_eq.left
  apply beta_eq.eval
  apply is_eval_once.k
  apply beta_eq.trans
  apply beta_eq.m_distributes
  cases h_t
  apply beta_eq.symm
  apply beta_eq.trans
  apply beta_eq.left
  apply beta_eq.eval
  apply is_eval_once.m_m
  apply beta_eq.trans
  apply beta_eq.eval
  apply is_eval_once.s
  apply beta_eq.trans
  apply beta_eq.left
  apply beta_eq.eval
  apply is_eval_once.k
  apply beta_eq.trans
  apply beta_eq.right
  apply beta_eq.eval
  apply is_eval_once.m_k
  apply beta_eq.rfl
  cases h_t
  apply valid_judgment_hard.beta_eq
  apply valid_judgment_hard.call
  apply valid_judgment_hard.call
  apply valid_judgment_hard.s
  apply beta_eq.trans
  apply beta_eq.eval
  apply is_eval_once.s
  apply beta_eq.trans
  apply beta_eq.left
  apply beta_eq.eval
  apply is_eval_once.k
  apply beta_eq.eval
  apply is_eval_once.m_call
  apply beta_eq.rfl
  apply beta_eq.symm
  apply beta_eq.trans
  apply beta_eq.m_distributes
  apply beta_eq.trans
  apply beta_eq.right
  apply beta_eq.eval
  apply is_eval_once.m_s
  apply beta_eq.symm
  apply beta_eq.trans
  apply beta_eq.left
  apply beta_eq.m_distributes
  apply beta_eq.trans
  apply beta_eq.m_distributes
  apply beta_eq.rfl

lemma progress : valid_judgment e t → (is_normal_n 0 e e ∨ ∃ e', is_eval_once e e') := by
  intro h_t
  induction h_t
  case call lhs t_lhs rhs t_t_call t' h_t_lhs h_t_call h_eval ih₁ ih₂ =>
    match h : SKM[(lhs rhs)] with
      | SKM[((K x) y)] =>
        right
        use x
        apply is_eval_once.k
      | SKM[(((S x) y) z)] =>
        right
        use SKM[((x z) (y z))]
        apply is_eval_once.s
      | SKM[(M e)] =>
        right
        use t
        apply valid_judgment.imp_m_eval
      | SKM[(lhs rhs)] =>
        sorry
      | x => sorry
  case s =>
    left
    apply s_stuck
  case k =>
    left
    apply k_stuck
  case m =>
    left
    apply m_stuck

