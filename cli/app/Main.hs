{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ApplicativeDo              #-}

module Main where

import Control.Monad.Trans.Except
import Text.Printf
import Cli.OptParse
import Cli.Exec
import Data.List (find)
import Data.Text (Text, pack)
import Control.Monad.Trans.Except
import Data.Maybe (fromMaybe, catMaybes)
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.IO.Class
import System.IO (putStr, hPutStrLn, stdout, stderr, hFlush, getLine)
import System.Exit (exitWith, ExitCode(ExitFailure))
import Skm.Ast
import Skm.Vm
import Skm.Eval (EvalConfig, EvalConfig(..))
import qualified Skm.Compiler.ProofGen as Proof
import qualified Skm.Compiler.Ast as CocAst
import qualified Skm.Compiler.Parse as CocP
import qualified Skm.Compiler.Translate as CocT
import Skm.Compiler.Ast (CompilationError)
import Skm.Parse (pExpr)
import Options.Applicative
import qualified Data.Text.IO as T
import Data.List (intercalate)
import Text.Megaparsec (parse, errorBundlePretty)

doMain :: ExceptT CompilationError IO ()
doMain = do
  cmd  <- liftIO readCommand

  case cmd of
    Eval (EvalOptions { nSteps = n, src = src, exeCfg = ExecConfig { stdPath }, mode = mode }) -> do
      eCfg <- getStreamRawPath stdPath >>= getEvalConfig stdPath
      e <- (ExceptT . pure) (case mode of
        Lc  -> parseResultToCompilationResult (parseProgramCoc streamStdinName rawE) >>= ccProgramCocToSk
        Raw -> parseResultToCompilationResult $ parseSk streamStdinName rawE)

      let e' = eval eCfg e

      liftIO $ print e'
    Prove (BetaEq BetaEqOptions { bFromSrc = fromSrc }) ->
      ((Proof.serialize . snd . Proof.cc) <$> readExpr fromSrc) >>= emit
    Compile (CompileOptions { ccSrc = src, dry = dry }) ->
      -- Dry indicates whether definitions should be collapsed into one body main expression
      -- or not.
      if not dry then
        ccLc src >>= (emit . show)
      else (do
        (fromStmts, fromE) <- readProgCoc src

        -- Fold all definitions such that they are inlined and compile main if it exists
        inlinedStmts       <- mapM (unwrapCompError . ccInline) fromStmts
        let ccE            = (((fmap (unwrapCompError . CocT.lift)) . CocAst.parseReadableExpr) <$> fromE)

        -- All compiled statements should be included
        -- but there might not be a main
        let fmtStmts = map show inlinedStmts
        let fmtLines = case ccE of
                         (Just fromE') -> (show fromE') : fmtStmts
                         Nothing       -> fmtStmts

        emit $ intercalate "\n" fmtLines)
    Repl opts -> repl prim opts
    _ -> empty
  where ccLc = readExprCoc
          >=> (hoistMaybe . CocAst.parseReadableExpr)
          >=> (unwrapCompError . CocT.lift)
          >=> (hoistMaybe . (fmap CocT.opt) . CocT.toSk)
        emit = liftIO . putStrLn

main :: IO ()
main = runMaybeT doMain >> (pure ())
