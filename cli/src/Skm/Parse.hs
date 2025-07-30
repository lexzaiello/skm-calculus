{-# LANGUAGE OverloadedStrings #-}

module Skm.Parse where

import Skm.Util.Parsing
import Skm.Ast (SkExpr(..))
import Text.Megaparsec

pCall :: Parser SkExpr
pCall = do
  lhs <- pExpr
  rhs <- pExpr

  pure $ Call lhs rhs

pExpr :: Parser SkExpr
pExpr = choice
  [ parens pCall
  , S <$ symbol "S"
  , K <$ symbol "K"
  , M <$ symbol "M"
  ]
