import SkLean.Ast2

namespace valid_judgment

theorem preservation_easy : valid_judgment e t → is_eval_once e e' → ∃ t', valid_judgment e' t' := by
  intro h_t h_eval
  induction h_eval
  cases h_t
  case k.call_k _ _ t_x h_t_x =>
    use t_x
  case s x y z n =>
    cases h_t
    case call_s t_call h_t_call h_u =>
      use t_call
  cases h_t
  cases h_t
  cases h_t
  cases h_t
  case left lhs lhs' rhs h_eval ih =>
    cases h_t
    cases h_eval
    case call_k.left x t_x n h_t_ lhs' h_eval =>
      cases h_eval
    cases h_eval
    case call_s.left x t_x n h_t_ lhs' h_eval =>
      cases h_eval
      case left x y z h_eval =>
        cases h_eval

end valid_judgment
