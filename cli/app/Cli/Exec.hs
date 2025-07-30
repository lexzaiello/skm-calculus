module Cli.Exec where

import Skm.Cli.OptParse (RawPath)
import Skm.Eval (EvalConfig)
import Skm.Compiler.Ast (CompilationError, CompilationResult)
import Skm.Ast as SkAst
import Skm.Ast (SkExpr)
import Skm.Compiler.Parse (Ident)
import Skm.Compiler.Ast (Stmt, HumanProgramCoc, RawProgramCoc, fromHumanExprCoc, HumanExprCoc, ExprCoc)

type ParseError = String
type Stream = String
type StreamName = String

type ParseResult = Except ParseError a

parseSk :: Stream -> ParseResult SkExpr

parseCocProgRaw :: Stream -> ParseResult RawProgramCoc

parseCocProgHuman :: Stream -> ParseResult HumanProgramCoc

parseCocExprHuman :: Stream -> ParseResult HumanExprCoc

ccRawCocToSk :: ExprCoc -> CompilationResult SkExpr

flattenDef :: Ident -> [Stmt a] -> CompilationResult a
flattenDef name stmts = (body <$> isDef matches stmts) >>= cc
  where body (Def _ bdy) = Just bdy
        body _           = Nothing

getStreamRawPath :: RawPath -> IO Stream

