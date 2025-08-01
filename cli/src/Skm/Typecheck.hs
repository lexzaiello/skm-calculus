module Skm.Typecheck where

import Skm.Ast (SkExpr)

data TypeError = Mismatched
  {
    expected :: SkExpr
  , found    :: SkExpr
  }

type TypeResult a = Either TypeError a
