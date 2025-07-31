module Cli.Repl where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import Skm.Eval (EvalConfig)
import Skm.Vm (eval)
import Skm.Compiler.Ast (CompilationError, parseResultToCompilationResult)
import System.IO (stdout, hFlush)
import Data.Text (pack)
import Cli.Exec

promptPs :: String
promptPs = ">> "

streamStdinName :: String
streamStdinName = "<STDIN>"

repl :: Maybe EvalConfig -> ExceptT CompilationError IO ()
repl eCfg = do
  liftIO $ putStr promptPs
  liftIO $ hFlush stdout
  rawE <- pack <$> liftIO getLine

  e <- case eCfg of
    Just cfg -> do
      (stmts, maybeE) <- parseProgramCoc streamStdinName rawE
      rawE <- hoistMaybe maybeE
      e  <- (hoistMaybe . CocAst.parseReadableExpr) rawE
      sk <- (hoistMaybe . ((pure . CocT.opt) <=< CocT.toSk <=< CocT.lift)) e

      pure sk
    Nothing -> (ExceptT . parseResultToCompilationResult) $ parseSk streamStdinName rawE

  let e' = eval eCfg e
  printEval e'

  repl eCfg opt
