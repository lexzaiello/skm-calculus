module Skm.Compiler.ProofGen where

import Skm.Ast (SkExpr(..))
import Skm.Eval (EvalConfig(..))

data EvalStep = SCall
  | KCall
  | MCall
  | MSCall
  | MKCall
  | MMCall

data BetaEqStep = Eval !EvalStep
  | Rfl
  | BLeft  !BetaEqStep
  | BRight !BetaEqStep
  | Trans !BetaEqStep !BetaEqStep

step :: EvalConfig -> SkExpr -> Maybe (SkExpr, EvalStep)
step _ (Call (Call K x) _y) = Just (x, KCall)
step _ (Call (Call (Call S x) y) z) = Just (Call (Call x z) (Call y z), SCall)
step cfg (Call M K) = Just (tK cfg, MKCall)
step cfg (Call M S) = Just (tS cfg, MSCall)
step cfg (Call M M) = Just (tM cfg, MMCall)
step cfg (Call M (Call lhs rhs)) = Just (Call (tOut cfg) (Call (Call M lhs) rhs), MCall)
step _ _ = Nothing

cc :: EvalConfig -> SkExpr -> (SkExpr, BetaEqStep)
cc cfg (Call lhs rhs) =
  case step cfg (Call lhs rhs) of
    Just (e', proof) ->
      let (e_final, rst) = cc cfg e' in
        (e_final, Trans (Eval proof) rst)
    Nothing ->
      let (rhs', proof_rhs) = cc cfg rhs in
        if rhs' /= rhs then
          let (e_final, rst) = cc cfg (Call lhs rhs') in
            (e_final, Trans (BRight proof_rhs) rst)
        else
          let (lhs', proof_lhs) = cc cfg lhs
              (e_final, rst)    = cc cfg (Call lhs' rhs) in
            (e_final, Trans (BLeft proof_lhs) rst)
cc _ e = (e, Rfl)

instance Show EvalStep where
  show SCall  = "is_eval_once.s"
  show KCall  = "is_eval_once.k"
  show MCall  = "is_eval_once.m_call"
  show MSCall = "is_eval_once.m_s"
  show MKCall = "is_eval_once.m_k"
  show MMCall = "is_eval_once.m_m"

instance Show BetaEqStep where
  show Rfl             = "beta_eq.rfl"
  show (BLeft e)       = "beta_eq.left  (" ++ show e   ++ ")"
  show (BRight e)      = "beta_eq.right (" ++ show e   ++ ")"
  show (Trans e_1 e_2) = "beta_eq.trans (" ++ show e_1 ++ ") (" ++ show e_2 ++ ")"
  show (Eval s)        = "beta_eq.eval  (" ++ show s   ++ ")"
