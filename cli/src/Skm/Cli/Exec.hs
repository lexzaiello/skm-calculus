{-# LANGUAGE OverloadedStrings #-}

module Skm.Cli.Exec where

import Control.Monad
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.List (find, foldl')
import Skm.Cli.OptParse (RawPath, EvalOptions, EvalOptions(redMode))
import Skm.Parse (pExpr)
import Skm.Eval (ReductionMode, EvalConfig(..))
import Skm.Util.Parsing (Parser)
import Skm.Ast (SkExpr)
import Skm.Compiler.Ast (CompilationError(..), parseResultToCompilationResult, NamedVar, ParseResult, HumanReadableExprCoc, fromHumanExprCoc, Ident, CompilationResult, Stmt(..), Program, fromHumanExprCoc, ExprCoc(..))
import Skm.Compiler.Parse (pProg)
import Skm.Compiler.Translate (toSk, lift, opt)
import qualified Skm.Compiler.Parse as SkP
import Text.Megaparsec (parse, errorBundlePretty)
import Data.Text.IO as TIO

type Stream = Text
type StreamName = String

doParse :: Parser a -> StreamName -> Stream -> ParseResult a
doParse parser fname stream = case parse parser fname stream of
  Left err  -> Left $ errorBundlePretty err
  Right er  -> Right er

parseSk :: StreamName -> Stream -> ParseResult SkExpr
parseSk = doParse pExpr

parseProgramCoc :: StreamName -> Stream -> ParseResult (Program HumanReadableExprCoc HumanReadableExprCoc)
parseProgramCoc = doParse pProg

parseExprCoc :: StreamName -> Stream -> ParseResult HumanReadableExprCoc
parseExprCoc = doParse SkP.pExpr

ccRawCocToSk :: HumanReadableExprCoc -> CompilationResult SkExpr
ccRawCocToSk = fromHumanExprCoc >=> lift >=> (fmap opt . toSk)

ccProgramCocToSk :: Program HumanReadableExprCoc HumanReadableExprCoc -> CompilationResult SkExpr
ccProgramCocToSk (stmts, body) = do
  let stmts' = flattenDefs stmts
  maybe (Left MissingBody) (Right . inlineCallDefsInExpr stmts') body
    >>= ccRawCocToSk

flattenDefs :: [Stmt HumanReadableExprCoc] -> [Stmt HumanReadableExprCoc]
flattenDefs stmts = foldl' (\acc x -> inlineStmt x : acc) [] stmts
  where inlineStmt (Def name body) = Def name $ inlineCallDefsInExpr stmts body

flattenProgram :: Program HumanReadableExprCoc HumanReadableExprCoc -> Program HumanReadableExprCoc HumanReadableExprCoc
flattenProgram (stmts, body) = (stmts', inlineCallDefsInExpr stmts' <$> body)
  where stmts'  = flattenDefs stmts

getStreamRawPath :: RawPath -> IO Stream
getStreamRawPath = TIO.readFile

-- Converts all const function calls to inline definition calls
-- where possible
inlineCallDefsInExpr :: [Stmt HumanReadableExprCoc] -> HumanReadableExprCoc -> HumanReadableExprCoc
inlineCallDefsInExpr defs = inlineDef
  where inlineDef v@(Var vr)    = fromMaybe v $ lookupDef defs vr
        inlineDef (App lhs rhs) = App  (inlineDef lhs) (inlineDef rhs)
        inlineDef (Fall binder bindTy body) = Fall binder (inlineDef <$> bindTy) (inlineDef body)
        inlineDef (Lam binder bindTy body)  = Lam binder  (inlineDef <$> bindTy) (inlineDef body)
        inlineDef e = e

lookupDef :: [Stmt HumanReadableExprCoc] -> Ident -> Maybe HumanReadableExprCoc
lookupDef stmts vr = bodyOf <$> find isMatchingDef stmts
  where isMatchingDef (Def name _) = vr == name
        bodyOf (Def _ body) = body

getEvalConfig :: ReductionMode -> StreamName -> Stream -> CompilationResult EvalConfig
getEvalConfig mode fname s = do
  (stmts, _)    <- parseResultToCompilationResult (flattenProgram <$> parseProgramCoc fname s)
  tk            <- lookupAndCc stmts "t_k"
  ts            <- lookupAndCc stmts "t_s"
  tm            <- lookupAndCc stmts "t_m"

  pure $ EvalConfig
    { tK    = tk
    , tS    = ts
    , tM    = tm
    , mode  = mode }
  where lookupAndCc stmts name =
          maybe (Left $ UnknownConst name) Right (lookupDef stmts name) >>= ccRawCocToSk
