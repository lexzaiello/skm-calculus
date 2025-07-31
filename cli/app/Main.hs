{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Main where

import Skm.Cli.OptParse
import Skm.Cli.Exec
import Skm.Cli.Repl (repl)
import qualified Data.Text.IO as TIO
import Control.Monad.Trans.Except
import Control.Monad.IO.Class
import System.IO (hPrint, stderr)
import Skm (ccResultToGenResult, execResultToGenResult, Error)
import Skm.Vm
import qualified Skm.Compiler.ProofGen as Proof
import Skm.Compiler.Ast (Stmt(..), parseResultToCompilationResult)
import Data.List (intercalate)

doMain :: ExceptT Error IO ()
doMain = do
  cmd  <- liftIO readCommand

  (case cmd of
    (Eval o@(EvalOptions { nSteps = n, src = src, execCfg = ExecConfig { stdPath = stdPath }, mode = mode, redMode = m })) -> do
      stdStream <- liftIO $ getStreamRawPath stdPath
      eCfg <- (ExceptT . pure . ccResultToGenResult) $ getEvalConfig m stdPath stdStream
      rawE <- liftIO $ TIO.readFile src
      let parsed = case mode of
                     Lc  -> parseResultToCompilationResult (parseProgramCoc src rawE) >>= ccProgramCocToSk
                     Raw -> parseResultToCompilationResult $ parseSk src rawE

      e <- ExceptT . pure . ccResultToGenResult $ parsed
      e' <- (ExceptT . pure . execResultToGenResult) $ eval eCfg e

      case e' of
        Just e' ->
          liftIO $ print e'
        Nothing ->
          pure ()
    Prove (BetaEq o@(EvalOptions { src = src, execCfg = ExecConfig { stdPath = stdPath }, mode = mode, redMode = m })) -> do
      stdStream <- liftIO $ getStreamRawPath stdPath
      eCfg <- (ExceptT . pure . ccResultToGenResult) $ getEvalConfig m stdPath stdStream
      rawE <- liftIO $ TIO.readFile src
      e <- (ExceptT . pure . ccResultToGenResult) (parseResultToCompilationResult $ parseSk src rawE)

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
    Repl (ReplOptions { mode = mode, execCfg = ExecConfig { stdPath = stdPath}, redMode = m }) -> do
      stdStream <- liftIO $ getStreamRawPath stdPath
      eCfg <- (ExceptT . pure . ccResultToGenResult) $ getEvalConfig m stdPath stdStream
      repl eCfg mode)
  where inlineStmt stmts (Def name body) = Def name $ inlineCallDefsInExpr stmts body
        ccStmt     (Def name body) = do
          body' <- ccRawCocToSk body
          pure $ Def name body'
        maybeEitherToEitherMaybe Nothing = Right Nothing
        maybeEitherToEitherMaybe (Just (Left e)) = Left e
        maybeEitherToEitherMaybe (Just (Right x)) = Right (Just x)

main :: IO ()
main = do
  e <- runExceptT doMain

  case e of
    Left e  -> hPrint stderr e
    Right _ -> pure ()
