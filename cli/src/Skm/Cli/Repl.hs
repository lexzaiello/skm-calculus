module Skm.Cli.Repl where

import Data.Either (fromLeft)
import Data.Maybe (fromMaybe)
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
import Skm.Vm (mkState, ExecError(..), outE, advance, advanceToEnd, eval, ExecState(..))
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

liftStateStack :: ExceptT ExecError (State s) out -> InputT (ExceptT Error (StateT s IO)) out
liftStateStack = lift . ExceptT . runExceptT . mapExceptT liftState . withExceptT ExecutionError
  where liftState :: State s (Either Error out) -> StateT s IO (Either Error out)
        liftState = mapStateT $ pure . runIdentity

execSession :: EvalConfig -> EvalMode -> InputT (ExceptT Error (StateT ExecState IO)) ()
execSession cfg eMode = do
  ctxExpr <- lift' $ gets outE
  minput <- getInputLine $ printf "%s %s" (either (const "") show ctxExpr) promptPs
  (case minput of
    Just "exit" -> pure ()
    Just "help" -> outputStrLn "exit | help | step | run | stack | register | log | cache"
    Just "step" -> do
      _ <- liftStateStack $ advance cfg
      execSession cfg eMode
    Just "run" -> do
      _ <- liftStateStack $ advanceToEnd cfg
      execSession cfg eMode
    Just "stack" -> do
      s <- lift' get
      outputStrLn $ (show . stack) s
      execSession cfg eMode
    Just "register" -> do
      s <- lift' get
      outputStrLn $ (show . register) s
      execSession cfg eMode
    Just "log" -> do
      s <- lift' get
      outputStrLn $ (show . trace) s
      execSession cfg eMode
    Just "cache" -> do
      s <- lift' get
      outputStrLn $ (show . cache) s
      execSession cfg eMode
    _ -> pure ())
  where lift'   = lift . lift

exprSession :: RawExpr -> EvalConfig -> EvalMode -> InputT (ExceptT Error IO) ()
exprSession ctxExpr cfg eMode = do
  minput <- getInputLine $ printf "%s %s" ctxExpr promptPs
  case minput of
    Just "exit" -> return ()
    Just "help" -> do
      outputStrLn "exit | help | parse | exec"
      exprSession ctxExpr cfg eMode
    Just "parse" -> do
      (lift . ExceptT . pure . liftErr . liftPErr) (case eMode of
        Raw -> fmap show $ parseSk streamStdinName $ pack ctxExpr
        Lc -> fmap show $ parseExprCoc streamStdinName $ pack ctxExpr) >>= outputStrLn
      exprSession ctxExpr cfg eMode
    Just "exec" -> do
      e <- (lift . ExceptT . pure . liftErr) (case eMode of
        Raw -> liftPErr $ parseSk streamStdinName $ pack ctxExpr
        Lc -> (liftPErr . parseExprCoc streamStdinName) (pack ctxExpr) >>= ccRawCocToSk)
      outputStrLn "Entered virtual machine session. Type \"help\" to see available commands."
      let e' = execSession cfg eMode
      lift $ ExceptT $ fmap fst (runStateT (runExceptT $ runInputT defaultSettings e') (mkState e))
      exprSession ctxExpr cfg eMode
    _ -> return ()
  where liftErr  = either (Left . CompError) Right
        liftPErr = either (Left . ParseFailure) Right

root :: EvalConfig -> EvalMode -> InputT (ExceptT Error IO) ()
root cfg md = do
  outputStrLn "Entered the SK(M) shell. Enter an expression to begin."
  minput <- getInputLine $ printf promptPs
  case minput of
    Just "exit" -> return ()
    Just input -> do
      outputStrLn "Entered expression session. Type \"help\" to see available commands."
      exprSession input cfg md
    Nothing -> return ()

repl :: EvalConfig -> EvalMode -> ExceptT Error IO ()
repl cfg md = runInputT defaultSettings $ root cfg md
