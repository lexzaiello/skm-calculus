import SkLean.Ast2

namespace valid_judgment

lemma imp_m : valid_judgment e t → _root_.beta_eq (trivial_typing e) t := by
  intro h_t
  induction h_t
  repeat exact beta_eq.rfl

lemma k_preserved : valid_judgment SKM[((((K α) β) x) y)] t → beta_eq t α := by
  intro h_t
  cases h_t
  case call t_rhs t_hs anything h_t_lhs h_t_y h_beq =>
    cases h_t_lhs
    case call h_t h_beq =>
      cases h_t
      case k h =>
        cases h
        case call h _ _ =>
          cases h
          

lemma well_typed_after_eval : is_eval_once e e' → valid_judgment e t → ∃ t', valid_judgment e' t' := by
  intro h_eval h_t
  match h : e with
    | SKM[((((K α) β) x) y)] =>
      
      sorry
    | SKM[((((((S α) β) γ) x) y) z)] => sorry
    | SKM[(M (lhs rhs))] => sorry

end valid_judgment
