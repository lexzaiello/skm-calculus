module Cli.Exec where

import Skm.Eval (EvalConfig)
import Skm.Compiler.Ast (CompilationError)
import Skm.Ast as SkAst
import Skm.Ast (SkExpr)
import Skm.Compiler.Ast as CocAst
import Skm.Compiler.Ast (fromHumanExprCoc, HumanExprCoc)

type ParseError = String
type Stream = String

parseSk :: Stream -> Except ParseError SkExpr

parseCocHuman :: HumanExprCoc -> 

data LcCompiler = LcCompiler EvalConfig

instance Compiler LcCompiler 

data Compiler = Raw
  | LcMode EvalConfig

compiler :: Maybe EvalConfig
compiler Just cfg = LcMode cfg
compiler Nothing  = Raw

parse :: Stream -> Compiler -> Except CompilationError 

readExpr :: String -> ExceptT IO String Expr
readExpr fname = do
  cts <- liftIO $ T.readFile fname
  case parse pExpr fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right e  ->
      pure e

type StreamName = String

parseSkStream :: StreamName -> Text -> ExceptT IO String Expr
parseSkStream fname cts = do
  case parse pExpr fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right e  ->
      pure e

parseProgCocStream :: StreamName -> Text -> ExceptT IO ([CocAst.Stmt], Maybe HumanExprCoc)
parseProgCocStream fname cts = do
  case parse CocP.pProg fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right (stmts, body)  ->
      let stmts' = foldl inlineAll [] stmts in do
        pure $ (stmts', CocP.inlineDefs stmts' <$> body)
  where inlineAll stmts (CocAst.Def id e) = (CocAst.Def id (CocP.inlineDefs stmts e)) : stmts

readCocSrc :: String -> ExceptT IO ([CocAst.Stmt], Maybe HumanExprCoc) String
readCocSrc fname = do
  cts <- liftIO $ T.readFile fname
  case parse CocP.pProg fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right (stmts, body)  ->
      let stmts' = foldl inlineAll [] stmts in do
        pure $ (stmts', CocP.inlineDefs stmts' <$> body)
  where inlineAll stmts (CocAst.Def id e) =
          let e' = CocP.inlineDefs stmts e in
            (CocAst.Def id e') : stmts

readExprCoc :: String -> MaybeT IO HumanExprCoc
readExprCoc fname = do
  (_, maybeE) <- readProgCoc fname
  hoistMaybe maybeE

cc :: HumanExprCoc -> Either CompilationError Expr
cc = ((pure . CocT.opt) <=< CocT.toSk) <=< CocT.lift <=< CocAst.parseReadableExpr

printEval :: Either ExecError (Maybe Expr) -> MaybeT IO ()
printEval (Left e) =
  liftIO (hPutStrLn stderr $
          printf "Execution failed. Offending opcode: %s. Backtrace: %s\n"
          (show $ offendingOp e)
          (show $ stackTrace e))
printEval (Right (Just e)) = liftIO $ putStrLn (show e)
printEval (Right Nothing)  = liftIO $ putStrLn "execution succeeded, but outputted nothing."

ccInline :: CocAst.Stmt -> Either CocAst.Stmt CompilationError
ccInline (CocAst.Def name value) = do
  value' <- (CocAst.parseReadableExpr >=> CocT.lift) value

  pure $ CocAst.Def name value'

flattenDef :: String -> [CocAst.Stmt] -> Either (CompilationError Maybe Expr)
flattenDef name stmts = (body <$> find matches stmts) >>= cc
  where body    (CocAst.Def _ bdy)   = bdy
        matches (CocAst.Def ident _) = ident == name

