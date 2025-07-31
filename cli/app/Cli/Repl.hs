module Cli.Repl where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import Skm.Eval (EvalConfig)
import Skm.Vm (eval)
import Skm.Compiler.Ast (CompilationError, parseResultToCompilationResult)
import System.IO (stdout, hFlush)
import Data.Text (pack)
import Cli.Exec
import Cli.OptParse (EvalMode(..))

promptPs :: String
promptPs = ">> "

streamStdinName :: String
streamStdinName = "<STDIN>"

repl :: EvalConfig -> EvalMode -> ExceptT CompilationError IO ()
repl eCfg mode = do
  liftIO $ putStr promptPs
  liftIO $ hFlush stdout
  rawE <- pack <$> liftIO getLine

  e <- ExceptT (case mode of
    Lc -> parseResultToCompilationResult $ parseProgramCoc streamStdinName rawE >>= ccProgramCocToSk
    Raw -> parseResultToCompilationResult $ parseSk streamStdinName rawE)

  let e' = eval eCfg e
  printEval e'

  repl eCfg opt
