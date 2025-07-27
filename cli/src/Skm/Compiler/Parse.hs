{-# LANGUAGE OverloadedStrings #-}

module Skm.Compiler.Parse where

import Control.Monad
import Data.List (find)
import Data.Maybe (fromMaybe)
import Skm.Util.Parsing
import qualified Skm.Compiler.Ast as Ast
import Skm.Compiler.Ast (ReadableExpr(..))
import Text.Megaparsec
import Text.Megaparsec.Char (alphaNumChar, char, letterChar)

pApp :: Parser Ast.ReadableExpr
pApp = parens $ do
  exprs <- some pExpr
  pure $ foldl1 HApp exprs

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
  ty <- pExpr
  _ <- sc

  pure (binder, ty)

pUntypedBinder :: Parser String
pUntypedBinder = pIdent

pVar :: Parser Ast.ReadableExpr
pVar = HVar <$> pIdent

type Binder = (String, Maybe Ast.ReadableExpr)

pBinder :: Parser Binder
pBinder = (try (unifyFromTyped <$> pTypedBinder) <|> (unifyFromUntyped <$> pUntypedBinder))
  where
    unifyFromTyped   (binderName, ty) = (binderName, Just ty)
    unifyFromUntyped binderName       = (binderName, Nothing)

pBinders :: Parser [Binder]
pBinders = many pBinder

pFall :: Parser Ast.ReadableExpr
pFall = do
  _ <- symbol "∀"
  (binder, maybeBty) <- pBinder
  _ <- sc
  _ <- symbol ","
  _ <- sc
  body <- pExpr
  -- Implicitly-typed, we don't recurse for ty
  pure (HLam binder maybeBty body)

currify :: [Binder] -> Ast.ReadableExpr -> Ast.ReadableExpr
currify ((binder, bty):xs) body = HLam binder bty (currify xs body)
currify [] body   = body

pLam :: Parser Ast.ReadableExpr
pLam = do
  _ <- symbol "λ" <|> symbol "\\"
  binders <- pBinders
  _ <- sc
  _ <- symbol "=>"
  _ <- sc
  body <- pExpr

  pure (currify binders body)

pExpr :: Parser Ast.ReadableExpr
pExpr = pApp <|> pComb <|> pLam <|> pFall <|> pVar <|> parens pExpr

pDef :: Parser Ast.Stmt
pDef = do
  _ <- symbol "def"
  name <- pIdent
  _ <- symbol ":="
  body <- pExpr

  pure $ Ast.Def name body

pProg :: Parser ([Ast.Stmt], Maybe Ast.ReadableExpr)
pProg = do
  sc
  stmts <- many pDef
  main  <- optional pExpr

  pure $ (stmts, main)

inlineDefs :: [Ast.Stmt] -> Ast.ReadableExpr -> Ast.ReadableExpr
inlineDefs defs (Ast.HVar ident) = fromMaybe (HVar ident) (thisDef >>= defBody)
  where thisDef = find isDef defs
        isDef   (Ast.Def id _) = id == ident
        isDef   _              = False
        defBody (Ast.Def _ body) = Just body
        defBody _                = Nothing
inlineDefs defs (Ast.HApp lhs rhs)         = Ast.HApp (inlineDefs defs lhs) (inlineDefs defs rhs)
inlineDefs defs (Ast.HFall binder ty body) = Ast.HFall binder (inlineDefs defs <$> ty) (inlineDefs defs body)
inlineDefs defs (Ast.HLam  binder ty body) = Ast.HLam  binder (inlineDefs defs <$> ty) (inlineDefs defs body)
inlineDefs defs e = e


