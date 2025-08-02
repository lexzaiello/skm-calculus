module Skm.Cli.Repl where

import Data.Functor.Identity
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.Trans.State
import Skm.Ast (SkExpr)
import Control.Monad.Trans.Class
import Text.Printf (printf)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import Skm.Eval (EvalConfig(..))
import Skm.Vm (ExecError(..), outE, advance, advanceToEnd, eval, ExecState(..))
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

liftStateStack :: ExceptT ExecError (State ExecState) () -> InputT (ExceptT Error (StateT ExecState IO)) ()
liftStateStack = lift . ExceptT . runExceptT . mapExceptT liftState . mapExceptT liftError
  where liftError :: Either ExecError a -> Either Error a
        liftError = either (Left . ExecutionError) Right
        liftState :: State ExecState (Either Error ()) -> StateT ExecState IO (Either Error ())
        liftState = mapStateT $ (\(s, x) -> pure (s, x)) . runIdentity

execSession :: EvalConfig -> EvalMode -> InputT (ExceptT Error (StateT ExecState IO)) ()
execSession cfg eMode = do
  ctxExpr <- lift' $ gets outE
  minput <- getInputLine $ printf "%s %s exit|step|run|cache|stack|register|log" (show ctxExpr) promptPs
  (case minput of
    Just "step" -> do
      advance cfg
      execSession cfg eMode
    Just "run" -> do
      lift' $ advanceToEnd cfg
      execSession cfg eMode
    Just "stack" -> do
      s <- lift' get
      stack s
    Just "register" -> do
      s <- lift' get
      stack s
    Just "log" -> do
      s <- lift' get
      trace s
    Just "cache" -> do
      s <- lift' get
      cache s
    _ -> pure ())
  where lift'   = lift . lift
        

exprSession :: RawExpr -> EvalConfig -> EvalMode -> InputT (ExceptT Error IO) ()
exprSession ctxExpr cfg eMode = do
  minput <- getInputLine $ printf "%s %s exit|parse|exec" ctxExpr promptPs
  case minput of
    Just "exit" -> return ()
    Just "parse" ->
      (lift . ExceptT . pure . liftErr . liftPErr) (case eMode of
        Raw -> fmap show $ parseSk streamStdinName $ pack ctxExpr
        Lc -> fmap show $ parseExprCoc streamStdinName $ pack ctxExpr) >>= outputStrLn
    Just "exec" -> do
      e <- (lift . ExceptT . pure . liftErr) (case eMode of
        Raw -> liftPErr $ parseSk streamStdinName $ pack ctxExpr
        Lc -> (liftPErr . parseExprCoc streamStdinName) (pack ctxExpr) >>= ccRawCocToSk)
      
      pure ()
    Nothing -> return ()
  where liftErr  = either (Left . CompError) Right
        liftPErr = either (Left . ParseFailure) Right

root :: EvalConfig -> EvalMode -> InputT (ExceptT Error IO) ()
root cfg md = do
  minput <- getInputLine $ printf promptPs
  case minput of
    Just "exit" -> return ()
    Just input ->
      exprSession input cfg md
    Nothing -> return ()

repl' :: EvalConfig -> EvalMode -> ExceptT Error IO ()
repl' cfg md = runInputT defaultSettings $ root cfg md
