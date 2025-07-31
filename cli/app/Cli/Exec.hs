{-# LANGUAGE OverloadedStrings #-}

module Cli.Exec where

import Control.Monad
import Data.Text (Text)
import Data.List (find)
import Cli.OptParse (RawPath)
import Skm.Parse (pExpr)
import Skm.Eval (EvalConfig(..))
import Skm.Util.Parsing (Parser)
import Skm.Ast (SkExpr)
import Skm.Compiler.Ast (CompilationError(..), parseResultToCompilationResult, NamedVar, ParseResult, HumanReadableExprCoc, fromHumanExprCoc, Ident, CompilationResult, Stmt(..), Program, fromHumanExprCoc, ExprCoc(..))
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

data NamedVarOrInlinedDef = Variable !NamedVar
  | InlinedDef !HumanReadableExprCoc

-- Converts all const function calls to inline definition calls
-- where possible
inlineCallDefsInExpr :: [Stmt HumanReadableExprCoc] -> HumanReadableExprCoc -> ExprCoc NamedVar NamedVarOrInlinedDef
inlineCallDefsInExpr defs = fmap inlineDef
  where inlineDef vr = maybe (Variable vr) InlinedDef $ lookupDef defs vr

lookupDef :: [Stmt HumanReadableExprCoc] -> Ident -> Maybe HumanReadableExprCoc
lookupDef stmts vr = bodyOf <$> find isMatchingDef stmts
  where isMatchingDef (Def name _) = vr == name
        bodyOf (Def _ body) = body

getEvalConfig :: StreamName -> Stream -> CompilationResult EvalConfig
getEvalConfig fname s = do
  (stmts, _)    <- parseResultToCompilationResult $ parseProgramCoc fname s
  arrowE        <- lookupAndCc stmts "arrow"
  tin           <- lookupAndCc stmts "t_in"
  tout          <- lookupAndCc stmts "t_out"
  tk            <- lookupAndCc stmts "t_k"
  ts            <- lookupAndCc stmts "t_s"
  tm            <- lookupAndCc stmts "t_m"

  pure $ EvalConfig
    { tIn   = tin
    , tOut  = tout
    , tK    = tk
    , tS    = ts
    , tM    = tm
    , arrow = arrowE }
  where lookupAndCc stmts name =
          maybe (Left $ UnknownConst name) Right (lookupDef stmts name) >>= ccRawCocToSk
