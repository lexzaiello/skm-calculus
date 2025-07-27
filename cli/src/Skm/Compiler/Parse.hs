{-# LANGUAGE OverloadedStrings #-}

module Skm.Compiler.Parse where

import Data.Text (Text, unpack)
import Data.List (elem)
import qualified Data.Set as Set
import Skm.Util.Parsing
import qualified Skm.Compiler.Ast as Ast
import Skm.Compiler.Ast (Expr(..), ReadableExpr(..))
import Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void
import Data.Char (isSpace)

reserved :: [Char]
reserved = ['λ', ':', '(', ')', '∀', 'S', 'K', 'M']

pLParen :: Parser ()
pLParen = symbol "(" >> (pure ())

pRParen :: Parser ()
pRParen = symbol ")" >> (pure ())

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

pIdent :: Parser String
pIdent = unpack <$> takeWhileP (Just " ") valid
  where valid s = (not (isSpace s)) && (not (s `elem` reserved))

pTypedBinder :: Parser (String, Ast.ReadableExpr)
pTypedBinder = parens (do
  _ <- sc
  binder <- pIdent
  _ <- sc
  _ <- pColon
  ty <- pTerm
  _ <- sc

  pure (binder, ty))

pUntypedBinder :: Parser String
pUntypedBinder = pIdent

pVar :: Parser Ast.ReadableExpr
pVar = HVar <$> pIdent

pBinders :: Parser [(String, Maybe Ast.ReadableExpr)]
pBinders = many $ spaces (try (unifyFromTyped <$> pTypedBinder) <|> (unifyFromUntyped <$> pUntypedBinder))
  where
    spaces                            = between (many sc) (many sc)
    unifyFromTyped   (binderName, ty) = (binderName, Just ty)
    unifyFromUntyped binderName       = (binderName, Nothing)

-- Final body, binders to go
currifyFall :: Ast.ReadableExpr -> [(String, Maybe Ast.ReadableExpr)] -> Ast.ReadableExpr
currifyFall bdy ((binder, maybeType):xs) = HFall binder maybeType (currifyFall bdy xs)
currifyFall bdy []                       = bdy

currifyLam :: Ast.ReadableExpr -> [(String, Maybe Ast.ReadableExpr)] -> Ast.ReadableExpr
currifyLam bdy ((binder, maybeType):xs) = HLam binder maybeType (currifyLam bdy xs)
currifyLam bdy []                       = bdy

pFall :: Parser Ast.ReadableExpr
pFall = do
  _ <- symbol "∀"
  binders <- pBinders
  _ <- sc
  _ <- symbol ","
  _ <- sc
  body <- pTerm

  pure $ currifyFall body binders

pLam :: Parser Ast.ReadableExpr
pLam = do
  _ <- symbol "λ"
  binders <- pBinders
  _ <- sc
  _ <- symbol "=>"
  _ <- sc
  body <- pTerm

  pure $ currifyLam body binders

pTerm :: Parser Ast.ReadableExpr
pTerm = choice
  [ pApp
  , pComb
  , pVar
  , pLam
  , pFall
  ]

parse :: Parser Ast.ReadableExpr
parse = pTerm
