{-# LANGUAGE OverloadedStrings #-}

module Skm.Compiler.Parse where

import qualified Data.Text as T
import Control.Monad
import Data.Char (isLetter, isAlphaNum)
import Data.List (find)
import Data.Maybe (fromMaybe)
import Skm.Util.Parsing
import qualified Skm.Compiler.Ast as Ast
import Skm.Compiler.Ast (ExprCoc, Binderless, DebruijnVar, NamedVar, Ident)
import Text.Megaparsec
import Text.Megaparsec.Char

pApp :: Parser (ExprCoc tBinder tVar)
pApp = parens $ do
  exprs <- some pExpr
  pure $ foldl1 HApp exprs

pComb :: Parser (ExprCoc tBinder tVar)
pComb = choice
  [ S <$ symbol "S"
  , K <$ symbol "K"
  , M <$ symbol "M"
  ]

pColon :: Parser ()
pColon = symbol ":" >> void

pIdent :: Parser Ident
pIdent = lexeme $ do
  first <- satisfy isLetter <?> "identifier start (letter)"
  rest  <- takeWhileP (Just "identifier continuation") isIdentChar
  return $ T.cons first rest
  where isIdentChar c = isAlphaNum c || c == '_'

pTypedBinder :: Parser (Ident, Ast.HumanExprCoc)
pTypedBinder = parens $ do
  _ <- sc
  binder <- pIdent
  _ <- sc
  _ <- pColon
  ty <- pExpr
  _ <- sc

  pure (binder, ty)

pUntypedBinder :: Parser Ident
pUntypedBinder = pIdent

pVar :: Parser Ast.HumanExprCoc
pVar = HVar <$> pIdent

type Binder = (Ident, Maybe Ast.HumanExprCoc)

pBinder :: Parser Binder
pBinder = try (unifyFromTyped <$> pTypedBinder) <|> (unifyFromUntyped <$> pUntypedBinder)
  where
    unifyFromTyped   (binderName, ty) = (binderName, Just ty)
    unifyFromUntyped binderName       = (binderName, Nothing)

pBinders :: Parser [Binder]
pBinders = many pBinder

pFall :: Parser Ast.HumanExprCoc
pFall = do
  _ <- symbol "∀"
  (binder, maybeBty) <- pBinder
  _ <- sc
  _ <- symbol ","
  _ <- sc
  body <- pExpr
  -- Implicitly-typed, we don't recurse for ty
  pure (HLam binder maybeBty body)

currify :: [Binder] -> Ast.HumanExprCoc -> Ast.HumanExprCoc
currify ((binder, bty):xs) body = HLam binder bty (currify xs body)
currify [] body   = body

pLam :: Parser Ast.HumanExprCoc
pLam = do
  _ <- symbol "λ" <|> symbol "\\"
  binders <- pBinders
  _ <- sc
  _ <- symbol "=>"
  _ <- sc
  body <- pExpr

  pure (currify binders body)

pExpr :: Parser Ast.HumanExprCoc
pExpr = pApp <|> pComb <|> pLam <|> pFall <|> pVar <|> parens pExpr

pDef :: Parser Ast.Stmt
pDef = do
  _ <- symbol "def"
  name <- pIdent
  _ <- symbol ":="
  body <- pExpr

  pure $ Ast.Def name body

pProg :: Parser ([Ast.Stmt], Maybe Ast.HumanExprCoc)
pProg = do
  sc
  stmts <- many pDef
  main  <- optional pExpr

  pure (stmts, main)

inlineDefs :: [Ast.Stmt] -> Ast.HumanExprCoc -> Ast.HumanExprCoc
inlineDefs defs (Ast.HVar ident) = fromMaybe (HVar ident) (thisDef >>= defBody)
  where thisDef = find isDef defs
        isDef   (Ast.Def name _) = name == ident
        defBody (Ast.Def _ body) = Just body
inlineDefs defs (Ast.HApp lhs rhs)         = Ast.HApp (inlineDefs defs lhs) (inlineDefs defs rhs)
inlineDefs defs (Ast.HFall binder ty body) = Ast.HFall binder (inlineDefs defs <$> ty) (inlineDefs defs body)
inlineDefs defs (Ast.HLam  binder ty body) = Ast.HLam  binder (inlineDefs defs <$> ty) (inlineDefs defs body)
inlineDefs _ e = e


