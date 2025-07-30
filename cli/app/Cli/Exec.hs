{-# LANGUAGE OverloadedStrings #-}

module Cli.Exec where

import Cli.OptParse (RawPath)
import Skm.Parse (pExpr)
import Skm.Eval (EvalConfig)
import Skm.Ast as SkAst
import Skm.Ast (SkExpr)
import Skm.Compiler.Ast (HumanReadableExprCoc, fromHumanExprCoc, Ident, CompilationError, CompilationResult, Stmt(..), Program, fromHumanExprCoc, ExprCoc)
import Skm.Compiler.Parse (pProg)
import Skm.Compiler.Translate (toSk)
import qualified Skm.Compiler.Parse as SkP
import Text.Megaparsec (parse)
import Data.Text.IO as TIO

type ParseError = String
type Stream = String
type StreamName = String

type ParseResult a = Either ParseError a

parseSk :: StreamName -> Stream -> ParseResult SkExpr
parseSk = parse pExpr

parseProgramCoc :: StreamName -> Stream -> Either tErr (ExprCoc tBinder tVar)
parseProgramCoc = parse pProg

parseExprCoc :: StreamName -> Stream -> Either tErr (ExprCoc tBinder tVar)
parseExprCoc = parse SkP.pExpr

ccRawCocToSk :: HumanReadableExprCoc -> CompilationResult SkExpr
ccRawCocToSk = fromHumanExprCoc >>= toSk

flattenDef :: Ident -> [Stmt a] -> CompilationResult a
flattenDef name stmts = body isDef matches stmts >>= cc
  where body (Def _ bdy) = Just bdy
        body _           = Nothing

getStreamRawPath :: RawPath -> IO Stream
getStreamRawPath = TIO.readFile
