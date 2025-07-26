module Skm.Parsing where

import Data.Text (Text)
import Data.Void
import qualified Data.Text as T
import Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as C

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "/-" "-/")

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
