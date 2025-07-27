{-# LANGUAGE OverloadedStrings #-}

module Skm.Compiler.Parse where

import Skm.Util.Parsing
import qualified Skm.Compiler.Ast as Ast
import Skm.Compiler.Ast (Token(..), Expr(..), ReadableExpr(..))
import Text.Megaparsec
import Data.Char (isSpace)

ptAtom :: Parser Ast.Token
ptAtom = choice
  [ LParen   <$ single "("
  , RParen   <$ single ")"
  , Ts       <$ single "S"
  , Tk       <$ single "K"
  , Tm       <$ single "M"
  , Space    <$ single " "
  , Lambda   <$ single "λ"
  , FatArrow <$ single "=>"
  , Def      <$ single "def"
  , Colon    <$ single ":"
  , Eq       <$ single "="
  , TFall    <$ single "∀"
  , Comma    <$ single ","
  ]

pToken :: Parser Ast.Token
pToken = try ptAtom <|> (Ident <$> (some (satisfy (not . isSpace))))

type Parser' = Parsec Void [Token]

pApp :: Parser' Ast.ReadableExpr
pApp = do
  lhs <- pTerm
  rhs <- pTerm

  pure $ (HApp lhs rhs)

pIdent :: Parser' String
pIdent = token toIdent
  where toIdent (Ident ident) = Just ident
        toIdent _             = Nothing

pVar :: Parser' Ast.ReadableExpr
pVar = HVar <$> pIdent

pComb :: Parser' Ast.ReadableExpr
pComb = choice
  [ Hs <$ single Ts
  , Hk <$ single Tk
  , Hm <$ single Tm
  ]

advanceWhitespace :: Parser' Ast.ReadableExpr
advanceWhitespace = takeWhileP isSpace
  where isSpace Space = True
        isSpace _     = False

pColon :: Parser' Ast.ReadableExpr
pColon = single Colon

pTypedBinder :: Parser' (String, Ast.ReadableExpr)
pTypedBinder = do
  _ <- single LParen
  _ <- advanceWhitespace
  binder <- pIdent
  _ <- advanceWhitespace
  _ <- pColon
  ty <- pTerm
  _ <- advanceWhitespace
  _ <- single RParen

  pure (binder, ty)

pUntypedBinder :: Parser' String
pUntypedBinder = single pIdent

pBinders :: Parser' (List (String, Maybe Ast.ReadableExpr))
pBinders = spaces (try (unifyFromTyped <$> pTypedBinder) <|> (unifyFromUntyped <$> pUntypedBinder))
  spaces = between (many (single Space)) (many (single Space))
  where
    unifyFromTyped   (binderName, ty) = (binderName, Just ty)
    unifyFromUntyped binderName       = (binderName, Nothing)

-- Final body, binders to go
currifyFall :: Ast.ReadableExpr -> [Ast.ReadableExpr] -> Ast.ReadableExpr
currifyFall bdy (binder, maybeType):xs = HFall binder maybeType (currifyFall bdy xs)
currifyFall bdy []                     = bdy

currifyLam :: Ast.ReadableExpr -> [Ast.ReadableExpr] -> Ast.ReadableExpr
currifyFall bdy (binder, maybeType):xs = HLam binder maybeType (currifyLam bdy xs)
currifyFall bdy []                     = bdy

pFall :: Parser' Ast.ReadableExpr
pFall = do
  _ <- single TFall
  binders <- pBinders
  _ <- advanceWhitespace
  _ <- single Comma
  _ <- advanceWhitespace
  body <- pTerm

  pure $ currifyFall binders body

pLam :: Parser' Ast.ReadableExpr
pLam = do
  _ <- single Lambda
  binders <- pBinders
  _ <- advanceWhitespace
  _ <- single FatArrow
  _ <- advanceWhitespace
  body <- pTerm

  pure $ currifyLam binders body

pTerm :: Parser' Ast.ReadableExpr
pTerm = choice
  [ pApp
  , pComb
  , pVar
  , pLam
  , pFall
  ]
