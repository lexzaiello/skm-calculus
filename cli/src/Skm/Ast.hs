module Skm.Ast where

data Expr =
  S
  | K
  | M
  | Call (Expr lhs) (Expr rhs)
  deriving (Eq)

instance Show Expr where
  show S = "S"
  show K = "K"
  show M = "M"
  show Call lhs rhs = "(" ++ show lhs ++ " " ++ show rhs ++ ")"
