module Skm.Ast where

data Expr =
  S
  | K
  | M
  | Call Expr Expr
  deriving (Eq)

instance Show Expr where
  show S              = "S"
  show K              = "K"
  show M              = "M"
  show (Call lhs rhs) = "(" ++ show lhs ++ " " ++ show rhs ++ ")"
