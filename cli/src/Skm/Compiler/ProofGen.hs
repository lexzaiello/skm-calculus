module Skm.Compiler.ProofGen where

import Skm.Ast
import Skm.Std

data EvalExpr = SCall
  | KCall
  | MCall
  | MSCall
  | MKCall
  | MMCall

data BetaEqExpr = Eval EvalExpr
  | Rfl
  | BLeft  BetaEqExpr
  | BRight BetaEqExpr
  | Trans BetaEqExpr BetaEqExpr

step :: Expr -> Maybe (Expr, EvalExpr)
step (Call (Call K x) _y) = Just (x, KCall)
step (Call (Call (Call S x) y) z) = Just ((Call (Call x z) (Call y z)), SCall)
step (Call M K) = Just (t_k, MKCall)
step (Call M S) = Just (t_s, MSCall)
step (Call M M) = Just (t_m, MMCall)
step (Call M (Call lhs rhs)) = Just ((Call t_out (Call (Call M lhs) rhs)), MCall)
step _ = Nothing

cc :: Expr -> (Expr, BetaEqExpr)
cc (Call lhs rhs) =
  case step (Call lhs rhs) of
    Just (e', proof) ->
      let (e_final, rst) = (cc e') in
        (e_final, Trans (Eval proof) rst)
    Nothing ->
      let (rhs', proof_rhs) = cc rhs in
        if rhs' /= rhs then
          let (e_final, rst) = (cc (Call lhs rhs')) in
            (e_final, Trans (BRight proof_rhs) rst)
        else
          let (lhs', proof_lhs) = cc lhs
              (e_final, rst)    = (cc (Call lhs' rhs)) in
            (e_final, Trans (BLeft proof_lhs) rst)
cc e = (e, Rfl)

serialize_eval :: EvalExpr -> String
serialize_eval SCall  = "is_eval_once.s"
serialize_eval KCall  = "is_eval_once.k"
serialize_eval MCall  = "is_eval_once.m_call"
serialize_eval MSCall = "is_eval_once.m_s"
serialize_eval MKCall = "is_eval_once.m_k"
serialize_eval MMCall = "is_eval_once.m_m"

serialize :: BetaEqExpr -> String
serialize Rfl             = "beta_eq.rfl"
serialize (BLeft e)       = "beta_eq.left  (" ++ serialize e         ++ ")"
serialize (BRight e)      = "beta_eq.right (" ++ serialize e         ++ ")"
serialize (Trans e_1 e_2) = "beta_eq.trans (" ++ serialize e_1       ++ ") (" ++ serialize e_2 ++ ")"
serialize (Eval s)        = "beta_eq.eval  (" ++ serialize_eval s    ++ ")"
