{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Main where

import Data.Either (fromRight)
import Text.Printf
import Cli.OptParse
import Cli.Exec
import Cli.Repl (repl)
import Data.Text (Text, pack)
import qualified Data.Text.IO as TIO
import Control.Monad.Trans.Except
import Data.Maybe (fromMaybe, catMaybes)
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.IO.Class
import System.IO (putStrLn, putStr, hPutStrLn, stdout, stderr, hFlush, getLine)
import System.Exit (exitWith, ExitCode(ExitFailure))
import Skm (ccResultToGenResult, Error)
import Skm.Ast
import Skm.Vm
import Skm.Eval (EvalConfig, EvalConfig(..))
import qualified Skm.Compiler.ProofGen as Proof
import qualified Skm.Compiler.Translate as CocT
import Skm.Compiler.Ast (Stmt(..), CompilationError, parseResultToCompilationResult)
import Skm.Parse (pExpr)
import Options.Applicative
import Data.List (intercalate)

doMain :: ExceptT Error IO ()
doMain = do
  cmd  <- liftIO readCommand

  (case cmd of
    (Eval (EvalOptions { nSteps = n, src = src, execCfg = ExecConfig { stdPath = stdPath }, mode = mode })) -> do
      stdStream <- liftIO $ getStreamRawPath stdPath
      eCfg <- (ExceptT . pure . ccResultToGenResult) $ getEvalConfig stdPath stdStream
      rawE <- liftIO $ TIO.readFile src
      let parsed = case mode of
                     Lc  -> parseResultToCompilationResult (parseProgramCoc src rawE) >>= ccProgramCocToSk
                     Raw -> parseResultToCompilationResult $ parseSk src rawE
      e <- ExceptT . pure . ccResultToGenResult $ parsed

      let e' = eval eCfg e

      liftIO $ print e'
    Prove (BetaEq (fromSrc, ExecConfig { stdPath = stdPath })) -> do
      stdStream <- liftIO $ getStreamRawPath stdPath
      eCfg <- (ExceptT . pure . ccResultToGenResult) $ getEvalConfig stdPath stdStream
      rawE <- liftIO $ TIO.readFile fromSrc
      e <- (ExceptT . pure . ccResultToGenResult) (parseResultToCompilationResult $ parseSk fromSrc rawE)

      liftIO $ (print . snd . Proof.cc eCfg) e
    Compile (CompileOptions { dry = dry, src = src }) -> do
      rawE <- liftIO $ TIO.readFile src
      -- Dry indicates whether definitions should be collapsed into one body main expression
      -- or not.
      if not dry then do
        prog <- (ExceptT . pure . ccResultToGenResult)
          $ parseResultToCompilationResult (parseProgramCoc src rawE) >>= ccProgramCocToSk
        liftIO $ print prog
      else (do
        (fromStmts, fromE) <- (ExceptT . pure . ccResultToGenResult . parseResultToCompilationResult) $ parseProgramCoc src rawE

        -- Fold all definitions such that they are inlined and compile main if it exists
        let inlinedStmts = foldl (\acc x -> inlineStmt acc x : acc) [] fromStmts
        ccStmts <- (ExceptT . pure . ccResultToGenResult) $ mapM ccStmt inlinedStmts
        ccE     <- (ExceptT . pure . ccResultToGenResult . maybeEitherToEitherMaybe) $ ccRawCocToSk . inlineCallDefsInExpr inlinedStmts <$> fromE

        -- All compiled statements should be included
        -- but there might not be a main
        let fmtStmts = map show ccStmts
        let fmtLines = case ccE of
                         (Just fromE') -> show fromE' : fmtStmts
                         Nothing       -> fmtStmts

        liftIO . putStrLn $ intercalate "\n" fmtLines)
    Repl (ReplOptions { mode = mode, execCfg = ExecConfig { stdPath = stdPath} }) -> do
      stdStream <- liftIO $ getStreamRawPath stdPath
      eCfg <- (ExceptT . pure . ccResultToGenResult) $ getEvalConfig stdPath stdStream
      repl eCfg mode)
  where inlineStmt stmts (Def name body) = Def name $ inlineCallDefsInExpr stmts body
        ccStmt     (Def name body) = do
          body' <- ccRawCocToSk body
          pure $ Def name body'
        maybeEitherToEitherMaybe Nothing = Right Nothing
        maybeEitherToEitherMaybe (Just (Left e)) = Left e
        maybeEitherToEitherMaybe (Just (Right x)) = Right (Just x)

main :: IO ()
main = void $ runExceptT doMain
