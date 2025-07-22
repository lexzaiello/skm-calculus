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

def i     : Expr := SKM[((S K) K)]
def arrow : Expr := SKM[((S (K ((S (K S)) K))) K)]
def t_in  : Expr := SKM[((S ((S K) K)) (K K))]
def t_out : Expr := SKM[((S i) (K (K i)))]

def t_k : Expr := SKM[((S ((S (K ((S (K ((S (K S)) K))) K))) ((S K) K))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K ((S (K ((S (K S)) K))) K))))) ((S ((S (K S)) (K K))) (K K))))) ((S (K K)) ((S K) K))))]
def t_s : Expr := SKM[((S ((S (K ((S (K ((S (K S)) K))) K))) ((S (K M)) ((S K) K)))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K ((S (K ((S (K S)) K))) K))))) ((S ((S (K S)) ((S (K K)) (K M)))) ((S ((S (K S)) (K K))) (K K)))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S (K K)) (K K)))) ((S (K K)) (K ((S (K ((S (K S)) K))) K))))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S (K K)) (K K)))) ((S (K K)) (K M)))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S (K K)) (K K))))) ((S (K K)) (K K)))))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S (K K)) (K K)))) ((S (K K)) (K ((S ((S K) K)) (K (K ((S K) K)))))))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S (K K)) (K K)))) ((S (K K)) (K ((S ((S K) K)) (K (K ((S K) K)))))))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S (K K)) (K K)))) ((S (K K)) (K M)))))) ((S ((S (K S)) ((S (K K)) (K K)))) ((S (K K)) ((S K) K))))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S (K K)) (K K))))) ((S (K K)) (K K)))))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S (K K)) (K K)))) ((S (K K)) (K ((S ((S K) K)) (K (K ((S K) K)))))))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S ((S (K S)) ((S (K K)) (K K)))) ((S (K K)) (K M)))))) ((S ((S (K S)) ((S (K K)) (K K)))) ((S ((S (K S)) (K K))) (K K))))))) ((S ((S (K S)) ((S ((S (K S)) ((S (K K)) (K S)))) ((S (K K)) (K K))))) ((S (K K)) (K K))))))))))]
def t_m : Expr := SKM[((S ((S (K ((S (K ((S (K S)) K))) K))) ((S (K M)) ((S K) K)))) ((S (K M)) ((S (K M)) ((S K) K))))]

inductive is_eval_once : Expr → Expr → Prop
  | k      : is_eval_once SKM[((K x) _y)] x
  | s      : is_eval_once SKM[(((S x) y) z)] SKM[((x z) (y z))]
  | m_call : is_eval_once SKM[(M (lhs rhs))] SKM[(t_out ((M lhs) rhs))]
  | m_k    : is_eval_once SKM[(M K)] t_k
  | m_s    : is_eval_once SKM[(M S)] t_s
  | m_m    : is_eval_once SKM[(M M)] t_m

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

inductive valid_judgment_hard : Expr → Expr → Prop
  | call : is_normal_n n SKM[(M (lhs rhs))] t'
    → n > 0
    → valid_judgment_hard t'' t'
    → valid_judgment_hard SKM[(lhs rhs)] SKM[((M lhs) rhs)]
  | s : valid_judgment_hard SKM[S] t_s
  | k : valid_judgment_hard SKM[K] t_k
  | m : valid_judgment_hard SKM[M] t_m
  | beta_eq : valid_judgment_hard e t₁
    → beta_eq t₁ t₂
    → valid_judgment_hard e t₂

namespace valid_judgment_hard

lemma weakening : valid_judgment_hard e t → valid_judgment_hard e t := by
  intro h
  induction h
  apply valid_judgment_hard.call
  case call.a h _ =>
    sorry
  case call.a h =>
    sorry
  case call.a h _ _ =>
    sorry
  repeat sorry

lemma imp_m_eval : valid_judgment_hard e t → _root_.beta_eq SKM[(M e)] t := by
  intro h_t
  induction h_t
  case call lhs t_lhs rhs t' h_t_lhs h_eval ih₁ =>
    apply beta_eq.trans
    apply beta_eq.eval
    apply is_eval_once.m_call
    apply beta_eq.trans
    apply beta_eq.left
    sorry
    sorry
    sorry
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
  sorry
  repeat sorry

end valid_judgment_hard

namespace beta_eq

@[simp]
lemma m_distributes : beta_eq SKM[((M lhs) rhs)] SKM[(M (lhs rhs))] := by
  apply beta_eq.symm
  apply beta_eq.eval
  sorry

end beta_eq

namespace valid_judgment


end valid_judgment

lemma preservation_k : valid_judgment_hard SKM[((K x) y)] α → valid_judgment_hard x α := by
  intro h_t
  cases h_t
  case call t_lhs t_t_call t' h_t_lhs h_t_call h_eval =>
    cases h_t_lhs
    sorry
    sorry
  sorry

lemma preservation_s : valid_judgment_hard SKM[(((S x) y) z)] α → valid_judgment_hard SKM[((x z) (y z))] α := by
  intro h_t
  cases h_t
  case call t_lhs t_t_call t' h_t_lhs h_t_call h_eval =>
    cases h_t_lhs
    repeat sorry
  sorry

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

lemma preservation : valid_judgment_hard e t → beta_eq e e' → valid_judgment_hard e' t := by
  intro h_t h_beq
  induction h_beq
  case rfl e'' =>
    exact h_t
  case eval e₁ e₂ h_eval =>
    induction h_t
    case call =>
      sorry
    cases h_eval
    cases h_eval
    cases h_eval
    simp_all
    case beta_eq ih =>
      apply valid_judgment_hard.beta_eq
      exact ih
      case a h_beq =>
        exact h_beq
  repeat sorry

lemma progress : valid_judgment_hard e t → (is_normal_n 0 e e ∨ ∃ e', is_eval_step e e') := by
  intro h_t
  induction h_t
  repeat sorry

