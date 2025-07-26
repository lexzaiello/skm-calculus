{-# LANGUAGE OverloadedStrings #-}

module Skm.Compiler.Parse where

import Skm.Parsing
import Skm.Compiler.Ast
import Text.Megaparsec

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

pCall :: Parser Expr
pCall = do
  lhs <- pExpr
  rhs <- pExpr

  pure $ (Call lhs rhs)

pExpr :: Parser Expr
pExpr = choice
  [ parens pCall
  , S <$ symbol "S"
  , K <$ symbol "K"
  , M <$ symbol "M"
  ]
