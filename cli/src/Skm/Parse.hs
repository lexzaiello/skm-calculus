module Skm.Parse where

import Data.Maybe
import Skm.Ast
import Data.String
import Options.Applicative
import Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Text Text

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

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
