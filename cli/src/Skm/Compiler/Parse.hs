{-# LANGUAGE OverloadedStrings #-}

module Skm.Compiler.Parse where

import Skm.Util.Parsing
import Skm.Compiler.Ast
import Text.Megaparsec

pIdent :: Parser Text
pIdent = (lexeme . try) $ do
  name <- (:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum)
  if name `elem` reservedWords
    then fail $ "keyword " ++ show name ++ " cannot be an identifier"
    else return name

ptAtom :: Parser Token
ptAtom = choice
  [ LParen   <$ "("
  , RParen   <$ ")"
  , TS       <$ "S"
  , TK       <$ "K"
  , TM       <$ "M"
  , Space    <$ " "
  , Lambda   <$ "λ"
  , FatArrow <$ "=>"
  , Def      <$ "def"
  , Colon    <$ ":"
  , Eq       <$ "="
  , TFall    <$ "∀"
  , Comma    <$ ","
  ]

pToken :: Parser Token
pToken = try ptAtom <|> Ident

pCall :: Parser ReadableExpr
pCall = do
  lhs <- pExpr
  rhs <- pExpr

  pure $ (Call lhs rhs)

pExpr :: Parser ReadableExpr
pExpr = choice
  [ parens pCall
  , S <$ symbol "S"
  , K <$ symbol "K"
  , M <$ symbol "M"
  
  ]
