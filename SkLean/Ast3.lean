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

#check @beta_eq.trans

inductive is_normal_n : ℕ → Expr → Expr → Prop
  | stuck : (¬(∃ e', is_eval_once e e'))                 → is_normal_n 0 e e
  | succ  : is_eval_once e e' → is_normal_n n e' e_final → is_normal_n n.succ e e_final

inductive valid_judgment_hard : Expr → Expr → Prop
  | call    : is_eval_once SKM[(M (lhs rhs))] t_output
    → beta_eq SKM[(t_in ((M lhs) rhs))] SKM[(M rhs)]
    → valid_judgment_hard SKM[(lhs rhs)] SKM[(M (lhs rhs))]
  | s       : valid_judgment_hard SKM[S] t_s
  | k       : valid_judgment_hard SKM[K] t_k
  | m       : valid_judgment_hard SKM[M] t_m
  | beta_eq : valid_judgment_hard e t₁
    → beta_eq t₁ t₂
    → valid_judgment_hard e t₂

namespace valid_judgment_hard

lemma imp_m_eval : valid_judgment_hard e t → _root_.beta_eq SKM[(M e)] t := by
  intro h_t
  induction h_t
  apply _root_.beta_eq.rfl
  apply _root_.beta_eq.eval
  apply is_eval_once.m_s
  apply _root_.beta_eq.eval
  apply is_eval_once.m_k
  apply _root_.beta_eq.eval
  apply is_eval_once.m_m
  case beta_eq e t₁ t₂ h_t₁ h_beq ih =>
    apply _root_.beta_eq.trans
    exact ih
    exact h_beq

end valid_judgment_hard

namespace beta_eq

@[simp]
lemma m_distributes : beta_eq SKM[(t_out ((M lhs) rhs))] SKM[(M (lhs rhs))] := by
  apply beta_eq.symm
  apply beta_eq.eval
  apply is_eval_once.m_call

end beta_eq

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

