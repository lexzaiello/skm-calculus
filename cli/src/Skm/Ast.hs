{-# LANGUAGE DeriveGeneric #-}

module Skm.Ast where

import GHC.Generics (Generic)
import Data.Hashable

data Expr = S
  | K
  | M
  | Call Expr Expr
  deriving (Eq, Generic)

instance Show Expr where
  show S              = "S"
  show K              = "K"
  show M              = "M"
  show (Call lhs rhs) = "(" ++ show lhs ++ " " ++ show rhs ++ ")"

instance Hashable Expr
