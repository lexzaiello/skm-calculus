module Skm.Parse where

import Skm.Ast
import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as C

type Parser = Parsec Text Text

sc :: Parser ()
sc = L.space C.space1 empty empty

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol (T.pack "(")) (symbol (T.pack ")"))

pCall :: Parser Expr
pCall = do
  lhs <- pExpr
  rhs <- pExpr

  pure $ (Call lhs rhs)

pExpr :: Parser Expr
pExpr = choice
  [ parens pCall
  , S <$ symbol (T.pack "S")
  , K <$ symbol (T.pack "K")
  , M <$ symbol (T.pack "M")
  ]
