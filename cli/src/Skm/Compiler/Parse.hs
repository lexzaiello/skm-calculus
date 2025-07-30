{-# LANGUAGE OverloadedStrings #-}

module Skm.Compiler.Parse where

import qualified Data.Text as T
import Control.Monad
import Data.Char (isLetter, isAlphaNum)
import Data.List (find)
import Data.Maybe (fromMaybe)
import Skm.Util.Parsing
import Skm.Compiler.Ast (OptionalTy(..), Ctx, Program, Stmt(..), HumanReadableExprCoc, ExprCoc(..), Binderless, DebruijnVar, NamedVar, Ident)
import Text.Megaparsec
import Text.Megaparsec.Char

pApp :: Parser HumanReadableExprCoc
pApp = parens $ do
  exprs <- some pExpr
  pure $ foldl1 App exprs

pComb :: Parser (ExprCoc tBinder tVar)
pComb = choice
  [ S <$ symbol "S"
  , K <$ symbol "K"
  , M <$ symbol "M"
  ]

pColon :: Parser ()
pColon = void $ symbol ":"

pIdent :: Parser Ident
pIdent = lexeme $ do
  first <- satisfy isLetter <?> "identifier start (letter)"
  rest  <- takeWhileP (Just "identifier continuation") isIdentChar
  return $ T.cons first rest
  where isIdentChar c = isAlphaNum c || c == '_'

pTypedBinder :: Parser (Ident, HumanReadableExprCoc)
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

pVar :: Parser HumanReadableExprCoc
pVar = Var <$> pIdent

type OptionallyTypedBinder = (Ident, OptionalTy HumanReadableExprCoc)

pBinder :: Parser OptionallyTypedBinder
pBinder = try (unifyFromTyped <$> pTypedBinder) <|> (unifyFromUntyped <$> pUntypedBinder)
  where
    unifyFromTyped   (binderName, ty) = (binderName, (OptionalTy . Just) ty)
    unifyFromUntyped binderName       = (binderName, OptionalTy Nothing)

pBinders :: Parser [OptionallyTypedBinder]
pBinders = many pBinder

pFall :: Parser HumanReadableExprCoc
pFall = do
  _ <- symbol "∀"
  (binder, maybeBty) <- pBinder
  _ <- sc
  _ <- symbol ","
  _ <- sc
  body <- pExpr
  -- Implicitly-typed, we don't recurse for ty
  pure (Lam binder maybeBty body)

currify :: Ctx OptionallyTypedBinder -> HumanReadableExprCoc -> HumanReadableExprCoc
currify ((binder, bty):xs) body = Lam binder bty (currify xs body)
currify [] body   = body

pLam :: Parser HumanReadableExprCoc
pLam = do
  _ <- symbol "λ" <|> symbol "\\"
  binders <- pBinders
  _ <- sc
  _ <- symbol "=>"
  _ <- sc
  body <- pExpr

  pure (currify binders body)

pExpr :: Parser HumanReadableExprCoc
pExpr = pApp <|> pComb <|> pLam <|> pFall <|> pVar <|> parens pExpr

pDef :: Parser (Stmt HumanReadableExprCoc)
pDef = do
  _ <- symbol "def"
  name <- pIdent
  _ <- symbol ":="
  body <- pExpr

  pure $ Def name body

pProg :: Parser (Program HumanReadableExprCoc HumanReadableExprCoc)
pProg = do
  sc
  stmts <- many pDef
  main  <- optional pExpr

  pure (stmts, main)
