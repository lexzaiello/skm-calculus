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
import Text.Megaparsec.Char (alphaNumChar, char, letterChar)
import Data.Void
import Data.Char (isSpace)

pLParen :: Parser ()
pLParen = symbol "(" >> (pure ())

pRParen :: Parser ()
pRParen = symbol ")" >> (pure ())

pApp :: Parser Ast.ReadableExpr
pApp = parens $ do
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
pIdent = lexeme $ do
  first <- letterChar <|> char '_'
  rest <- many (alphaNumChar <|> char '_')
  return $ (first : rest)

pTypedBinder :: Parser (String, Ast.ReadableExpr)
pTypedBinder = parens $ do
  _ <- sc
  binder <- pIdent
  _ <- sc
  _ <- pColon
  ty <- pTerm
  _ <- sc

  pure (binder, ty)

pUntypedBinder :: Parser String
pUntypedBinder = pIdent

pVar :: Parser Ast.ReadableExpr
pVar = HVar <$> pIdent

pBinder :: Parser (String, Maybe Ast.ReadableExpr)
pBinder = (try (unifyFromTyped <$> pTypedBinder) <|> (unifyFromUntyped <$> pUntypedBinder))
  where
    unifyFromTyped   (binderName, ty) = (binderName, Just ty)
    unifyFromUntyped binderName       = (binderName, Nothing)

pFall :: Parser Ast.ReadableExpr
pFall = do
  _ <- symbol "∀"
  (binder, maybeBty) <- pBinder
  _ <- sc
  _ <- symbol ","
  _ <- sc
  body <- pTerm
  -- Implicitly-typed, we don't recurse for ty
  pure (HLam binder maybeBty body)

pLam :: Parser Ast.ReadableExpr
pLam = do
  _ <- symbol "λ"
  (binder, maybeBty) <- pBinder
  _ <- sc
  _ <- symbol "=>"
  _ <- sc
  body <- pTerm

  pure (HLam binder maybeBty body)

pTerm :: Parser Ast.ReadableExpr
pTerm = choice
  [ pApp
  , pComb
  , pLam
  , pFall
  , pVar
  ]

parse :: Parser Ast.ReadableExpr
parse = choice
  [ pComb
  , pApp
  , pLam
  , pFall
  ]
