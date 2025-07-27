{-# LANGUAGE OverloadedStrings #-}

module Skm.Compiler.Parse where

import qualified Data.Set as Set
import Skm.Util.Parsing
import qualified Skm.Compiler.Ast as Ast
import Skm.Compiler.Ast (Token(..), Expr(..), ReadableExpr(..))
import Text.Megaparsec
import Data.Void
import Data.Char (isSpace)

reserved = ["λ", ":", "=>", 

pLParen :: Parser ()
pLParen = symbol "("

pRParen :: Parser ()
pRParen = symbol ")"

pApp :: Parser Ast.ReadableExpr
pApp = do
  lhs <- pTerm
  rhs <- pTerm

  pure $ (HApp lhs rhs)

pComb :: Parser Ast.ReadableExpr
pComb = choice
  [ Hs <$ symbol "S"
  , Hk <$ symbol "K"
  , Hm <$ symbol "M"
  ]

pColon :: Parser ()
pColon = symbol ":" >> (pure ())

pIdent :: Parser ()
pIdent = takeWhileP (Just " ") (not isSpace)

pTypedBinder :: Parser (String, Ast.ReadableExpr)
pTypedBinder = do
  _ <- pLParen
  _ <- sc
  binder <- pIdent
  _ <- advanceWhitespace
  _ <- pColon
  ty <- pTerm
  _ <- advanceWhitespace
  _ <- single RParen

  pure (binder, ty)

pUntypedBinder :: Parser' String
pUntypedBinder = pIdent

pBinders :: Parser' [(String, Maybe Ast.ReadableExpr)]
pBinders = many $ spaces (try (unifyFromTyped <$> pTypedBinder) <|> (unifyFromUntyped <$> pUntypedBinder))
  where
    spaces = between (many (single Space)) (many (single Space))
    unifyFromTyped   (binderName, ty) = (binderName, Just ty)
    unifyFromUntyped binderName       = (binderName, Nothing)

-- Final body, binders to go
currifyFall :: Ast.ReadableExpr -> [(String, Maybe Ast.ReadableExpr)] -> Ast.ReadableExpr
currifyFall bdy ((binder, maybeType):xs) = HFall binder maybeType (currifyFall bdy xs)
currifyFall bdy []                       = bdy

currifyLam :: Ast.ReadableExpr -> [(String, Maybe Ast.ReadableExpr)] -> Ast.ReadableExpr
currifyLam bdy ((binder, maybeType):xs) = HLam binder maybeType (currifyLam bdy xs)
currifyLam bdy []                       = bdy

pFall :: Parser' Ast.ReadableExpr
pFall = do
  _ <- single TFall
  binders <- pBinders
  _ <- advanceWhitespace
  _ <- single Comma
  _ <- advanceWhitespace
  body <- pTerm

  pure $ currifyFall body binders

pLam :: Parser' Ast.ReadableExpr
pLam = do
  _ <- single Lambda
  binders <- pBinders
  _ <- advanceWhitespace
  _ <- single FatArrow
  _ <- advanceWhitespace
  body <- pTerm

  pure $ currifyLam body binders

pTerm :: Parser' Ast.ReadableExpr
pTerm = choice
  [ pApp
  , pComb
  , pVar
  , pLam
  , pFall
  ]

parse :: Parser Ast.ReadableExpr
parse = do
  toks <- pTokens
  pTerm
