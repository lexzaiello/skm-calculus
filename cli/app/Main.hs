{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Main where

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
    Prove (BetaEq fromSrc) -> do
      rawE <- liftIO $ TIO.readFile fromSrc
      e <- (ExceptT . pure . ccResultToGenResult) (parseResultToCompilationResult $ parseSk fromSrc rawE)

      liftIO $ (print . snd . Proof.cc) e
    Compile (CompileOptions { dry = dry, src = src }) -> do
      rawE <- TIO.readFile src
      -- Dry indicates whether definitions should be collapsed into one body main expression
      -- or not.
      if not dry then do
        prog <- (ExceptT . pure . ccResultToGenResult)
          $ parseResultToCompilationResult (parseProgramCoc src rawE) >>= ccProgramCocToSk
        liftIO $ print prog
      else (do
        (fromStmts, fromE) <- parseProgramCoc src rawE

        -- Fold all definitions such that they are inlined and compile main if it exists
        let inlinedStmts = foldl (\acc x -> inlineStmt x : acc) [] fromStmts
        ccStmts          <- (ExceptT . pure . ccResultToGenResult) $ mapM ccStmt inlinedStmts
        let ccE          = inlineCallDefsInExpr ccStmts <$> fromE

        -- All compiled statements should be included
        -- but there might not be a main
        let fmtStmts = map show inlinedStmts
        let fmtLines = case ccE of
                         (Just fromE') -> show fromE' : fmtStmts
                         Nothing       -> fmtStmts

        liftIO . putStrLn $ intercalate "\n" fmtLines)
    Repl (ReplOptions { mode = mode, execCfg = execCfg }) -> do
      eCfg <- (liftIO . ccResultToGenResult) $ getEvalConfig stdPath <$> getStreamRawPath stdPath
      repl eCfg mode
    _ -> empty)
  where inlineStmt (Def name body) = Def name $ inlineCallDefsInExpr stmts body
        ccStmt     (Def name body) = do
          body' <- ccRawToSk body
          Def name $ either body id body'

main :: IO ()
main = void $ runMaybeT doMain
