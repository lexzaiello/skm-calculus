{-# LANGUAGE OverloadedStrings #-}

module Cli.Exec where

import Control.Monad
import Data.Text (Text)
import Cli.OptParse (RawPath)
import Skm.Parse (pExpr)
import Skm.Eval (EvalConfig)
import Skm.Ast as SkAst
import Skm.Util.Parsing (Parser)
import Skm.Ast (SkExpr)
import Skm.Compiler.Ast (ParseResult, ParseError, HumanReadableExprCoc, fromHumanExprCoc, Ident, CompilationError, CompilationResult, Stmt(..), Program, fromHumanExprCoc, ExprCoc)
import Skm.Compiler.Parse (pProg)
import Skm.Compiler.Translate (toSk)
import qualified Skm.Compiler.Parse as SkP
import Text.Megaparsec (parse, errorBundlePretty)
import Data.Text.IO as TIO

type Stream = Text
type StreamName = String

doParse :: Parser a -> StreamName -> Stream -> ParseResult a
doParse parser fname stream = case parse parser fname stream of
  Left err -> Left $ errorBundlePretty err
  Right e  -> Right e

parseSk :: StreamName -> Stream -> ParseResult SkExpr
parseSk = doParse pExpr

parseProgramCoc :: StreamName -> Stream -> ParseResult (Program HumanReadableExprCoc HumanReadableExprCoc)
parseProgramCoc = doParse pProg

parseExprCoc :: StreamName -> Stream -> ParseResult HumanReadableExprCoc
parseExprCoc = doParse SkP.pExpr

ccRawCocToSk :: HumanReadableExprCoc -> CompilationResult SkExpr
ccRawCocToSk = fromHumanExprCoc >=> toSk

getStreamRawPath :: RawPath -> IO Stream
getStreamRawPath = TIO.readFile

-- Converts all const fn calls to inline calls of the corresponding definition
inlineCallDefsIn :: [Stmt HumanReadableExprCoc] -> HumanReadableExprCoc -> CompilationResult HumanReadableExprCoc
inlineCallDefsIn defs (App lhs rhs) = do
  lhs' <- inlineCallDefsIn defs lhs
  rhs' <- inlineCallDefsIn defs lhs

  pure $ App lhs' rhs'
inlineCallDefsIn e = case e of

  where doInlineAbstr bindTy body = do
          bindTy' <- inlineCallDefsIn 

getEvalConfig :: StreamName -> Stream -> ComplationResult EvalConfig
getEvalConfig fname s = parseProgramCoc fname s
                          >>= 
