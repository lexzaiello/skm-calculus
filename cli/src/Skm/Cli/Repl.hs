module Skm.Cli.Repl where

import Data.Text (pack)
import Control.Monad.Trans.Class
import Text.Printf (printf)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import Skm.Eval (EvalConfig(..))
import Skm.Vm (eval)
import Skm (Error(..), ccResultToGenResult, execResultToGenResult)
import Skm.Compiler.Ast (CompilationError(..), parseResultToCompilationResult)
import System.IO (stdout, hFlush)
import Data.Text (pack)
import Skm.Cli.Exec
import Skm.Cli.OptParse (EvalMode(..))
import System.Console.Haskeline

type RawExpr = String

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

  liftIO $ print e'

  repl eCfg mode

exprSession :: RawExpr -> EvalConfig -> EvalMode -> InputT (ExceptT Error IO) ()
exprSession ctxExpr cfg eMode = do
  minput <- getInputLine $ printf "%s %s" ctxExpr promptPs
  case minput of
    Just "exit" -> return ()
    Just "parse" ->
      (lift . ExceptT . pure . liftErr) (case eMode of
        Raw -> fmap show $ parseSk streamStdinName $ pack ctxExpr
        Lc -> fmap show $ parseExprCoc streamStdinName $ pack ctxExpr) >>= outputStrLn
    Nothing -> return ()
  where liftErr  = either (Left . CompError . ParseFailure) Right

root :: EvalConfig -> EvalMode -> InputT (ExceptT Error IO) ()
root cfg mode = do
  minput <- getInputLine $ printf promptPs
  case minput of
    Just "exit" -> return ()
    Just input ->
      exprSession input cfg mode
    Nothing -> return ()

repl' :: EvalConfig -> EvalMode -> ExceptT Error IO ()
repl' cfg mode = liftIO $ runInputT defaultSettings (root cfg mode)
