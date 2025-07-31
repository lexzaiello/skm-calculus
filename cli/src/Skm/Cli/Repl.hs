module Skm.Cli.Repl where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import Skm.Eval (EvalConfig)
import Skm.Vm (eval)
import Skm (Error, ccResultToGenResult, execResultToGenResult)
import Skm.Compiler.Ast (CompilationError, parseResultToCompilationResult)
import System.IO (stdout, hFlush)
import Data.Text (pack)
import Skm.Cli.Exec
import Skm.Cli.OptParse (EvalMode(..))

promptPs :: String
promptPs = ">> "

streamStdinName :: String
streamStdinName = "<STDIN>"

repl :: EvalConfig -> EvalMode -> ExceptT Error IO ()
repl eCfg mode = do
  liftIO $ putStr promptPs
  liftIO $ hFlush stdout
  rawE <- pack <$> liftIO getLine

  e <- (ExceptT . pure . ccResultToGenResult) (case mode of
    Lc -> parseResultToCompilationResult (parseProgramCoc streamStdinName rawE) >>= ccProgramCocToSk
    Raw -> parseResultToCompilationResult $ parseSk streamStdinName rawE)

  e' <- (ExceptT . pure . execResultToGenResult) $ eval eCfg e

  case e' of
    Just e' ->
      liftIO $ print e'
    Nothing ->
      pure ()

  repl eCfg mode
