module Cli.Exec where

import Cli.OptParse (RawPath)
import Skm.Eval (EvalConfig)
import Skm.Compiler.Ast (CompilationError, CompilationResult)
import Skm.Ast as SkAst
import Skm.Ast (SkExpr)
import Skm.Compiler.Parse (Ident)
import Skm.Compiler.Ast (Stmt, Program, fromHumanExprCoc, ExprCoc)

type ParseError = String
type Stream = String
type StreamName = String

type ParseResult = Except ParseError a

parseSk :: Stream -> ParseResult SkExpr

parseProgramCoc :: Stream -> Either tErr (ExprCoc tBinder tVar)

parseExprCoc :: Stream -> Either tErr (ExprCoc tBinder tVar)

ccRawCocToSk :: ExprCoc -> CompilationResult SkExpr

flattenDef :: Ident -> [Stmt a] -> CompilationResult a
flattenDef name stmts = (body <$> isDef matches stmts) >>= cc
  where body (Def _ bdy) = Just bdy
        body _           = Nothing

getStreamRawPath :: RawPath -> IO Stream

