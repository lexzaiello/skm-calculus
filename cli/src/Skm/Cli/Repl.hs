module Skm.Cli.Repl where

import Data.List (intercalate)
import qualified Data.Text.IO as TIO
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Either (fromLeft)
import Data.Functor.Identity
import Data.Maybe (fromMaybe)
import Data.Text (pack)
import Skm (Error (..), ccResultToGenResult, execResultToGenResult)
import Skm.Ast (SkExpr)
import Skm.Cli.Exec
import Skm.Cli.OptParse (EvalMode (..))
import Skm.Compiler.Ast (CompilationError (..), parseResultToCompilationResult)
import Skm.Eval (EvalConfig (..))
import Skm.Vm (ExecError (..), ExecState (..), advance, advanceToEnd, eval, mkState, outE, reduceAll)
import System.Console.Haskeline
import System.IO (hFlush, stdout)
import Text.Printf (printf)

type RawExpr = String

type ProgramSrc = ([RawExpr], RawExpr)

promptPs :: String
promptPs = ">> "

streamStdinName :: String
streamStdinName = "<STDIN>"

liftStateStack :: ExceptT ExecError (State s) out -> InputT (ExceptT Error (StateT s IO)) out
liftStateStack = lift . ExceptT . runExceptT . mapExceptT liftState . withExceptT ExecutionError
  where
    liftState :: State s (Either Error out) -> StateT s IO (Either Error out)
    liftState = mapStateT $ pure . runIdentity

execSession :: EvalConfig -> EvalMode -> InputT (ExceptT Error (StateT ExecState IO)) ()
execSession cfg eMode = do
  ctxExpr <- lift' $ gets outE
  minput <- getInputLine $ printf "%s %s" (either (const "") show ctxExpr) promptPs
  ( case minput of
      Just "exit" -> pure ()
      Just "help" -> outputStrLn "exit | help | step | run | stack | register | log | cache"
      Just "step" -> do
        _ <- liftStateStack $ advance cfg
        execSession cfg eMode
      Just "run" -> do
        _ <- liftStateStack $ advanceToEnd cfg
        execSession cfg eMode
      Just "reduce" -> do
        _ <- liftStateStack $ reduceAll cfg
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
      _ -> pure ()
    )
  where
    lift' = lift . lift

exprSession :: ProgramSrc -> EvalConfig -> EvalMode -> InputT (ExceptT Error IO) ()
exprSession ctx@(stmts, ctxExpr) cfg eMode = do
  minput <- getInputLine $ printf "%s %s" ctxExpr promptPs
  case minput of
    Just "exit" -> return ()
    Just "help" -> do
      outputStrLn "exit | help | parse | exec | load <path>"
      exprSession (stmts, ctxExpr) cfg eMode
    Just "parse" -> do
      (lift . ExceptT . pure . liftErr . liftPErr)
        (case eMode of
           Raw -> fmap show $ parseSk streamStdinName $ pack ctxExpr
           Lc -> show <$> pProg)
        >>= outputStrLn
      exprSession (stmts, ctxExpr) cfg eMode
    Just "exec" -> do
      e <- (lift . ExceptT . pure . liftErr) (case eMode of
        Raw -> liftPErr $ parseSk streamStdinName $ pack ctxExpr
        Lc -> liftPErr pProg >>= ccProgramCocToSk)
      outputStrLn "Entered virtual machine session. Type \"help\" to see available commands."
      let e' = execSession cfg eMode
      lift $ ExceptT $ fmap fst (runStateT (runExceptT $ runInputT defaultSettings e') (mkState e))
      exprSession (stmts, ctxExpr) cfg eMode
    Just s -> do
      let cmd = words s
      case cmd of
        "load":src:_ -> do
          cts <- liftIO $ TIO.readFile src
          (stmts', _) <- (lift . ExceptT . pure . liftErr . liftPErr . parseProgramCoc src) cts
          exprSession (fmap show stmts' ++ stmts, ctxExpr) cfg eMode
    _ -> pure ()
  where liftErr  = either (Left . CompError) Right
        liftPErr = either (Left . ParseFailure) Right
        pProg    = parseProgramCoc streamStdinName (pack $ intercalate "\n" (show <$> stmts ++ [ctxExpr]))

root :: [RawExpr] -> EvalConfig -> EvalMode -> InputT (ExceptT Error IO) ()
root stmts cfg md = do
  minput <- getInputLine $ printf promptPs
  case minput of
    Just "exit" -> return ()
    Just input -> do
      let cmd = words input
      case cmd of
        "load":src:_ -> do
          cts <- liftIO $ TIO.readFile src
          (stmts', _) <- (lift . ExceptT . pure . liftErr . liftPErr . parseProgramCoc src) cts
          root (fmap show stmts' ++ stmts) cfg md
        _ -> do
          outputStrLn "Entered expression session. Type \"help\" to see available commands."
          exprSession ([], input) cfg md
          root stmts cfg md
    Nothing -> return ()
  where
    liftErr  = either (Left . CompError) Right
    liftPErr = either (Left . ParseFailure) Right

repl :: EvalConfig -> EvalMode -> ExceptT Error IO ()
repl cfg md = runInputT defaultSettings $ root [] cfg md
