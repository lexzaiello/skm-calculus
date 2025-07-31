{-# LANGUAGE DeriveGeneric #-}

module Skm.Ast where

import GHC.Generics (Generic)
import Data.Hashable

data SkExpr = S
  | K
  | M
  | Call !SkExpr !SkExpr
  deriving (Eq, Generic)

instance Show SkExpr where
  show S              = "S"
  show K              = "K"
  show M              = "M"
  show (Call lhs rhs) = "(" ++ show lhs ++ " " ++ show rhs ++ ")"

instance Hashable SkExpr
