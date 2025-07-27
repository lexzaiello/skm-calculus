{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ApplicativeDo              #-}

module Main where

import Data.Maybe (fromMaybe)
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.IO.Class
import System.IO (hPutStrLn, stderr)
import System.Exit (exitWith, ExitCode(ExitFailure))
import Skm.Ast
import Skm.Eval
import qualified Skm.Compiler.ProofGen as Proof
import qualified Skm.Compiler.Ast as CocAst
import qualified Skm.Compiler.Parse as CocP
import qualified Skm.Compiler.Translate as CocT
import Skm.Parse (pExpr)
import Options.Applicative
import qualified Data.Text.IO as T
import Data.List (intercalate)
import Text.Megaparsec (parse, errorBundlePretty)

data EvalOptions = EvalOptions
  { eNSteps :: (Maybe Int)
  , eSrc    :: String
  , lc      :: Bool
  }

data BetaEqOptions = BetaEqOptions
  { bFromSrc :: String }

data CompileOptions = CompileOptions
  { ccSrc :: String }

data ProveCommand = BetaEq BetaEqOptions

data Command = Eval EvalOptions
  | Prove ProveCommand
  | Compile CompileOptions

nStepsParser :: Parser (Maybe Int)
nStepsParser = optional $ option auto (
  long "n_steps"
  <> short 'n'
  <> help "Limit execution to a specific number of steps.")

srcParser :: Parser String
srcParser = argument str (metavar "FILE")

lcParser :: Parser (Maybe Bool)
lcParser = optional $ switch (long "lc" <> short 'l' <> help "Compile lambda calculus and evaluate as SKM")

evalParser :: Parser EvalOptions
evalParser = do
  src <- srcParser
  n   <- nStepsParser
  lc  <- lcParser

  pure $ EvalOptions { eSrc    = src
                     , eNSteps = n
                     , lc      = fromMaybe False lc
                     }

betaEqParser :: Parser BetaEqOptions
betaEqParser = do
  fromSrc <- srcParser

  pure $ BetaEqOptions { bFromSrc = fromSrc }

proveParser :: Parser ProveCommand
proveParser = hsubparser
  (command "beta_reduce" (info (BetaEq <$> betaEqParser) $ progDesc "Generate a proof of valid beta-reduction of an expression"))

compileParser :: Parser CompileOptions
compileParser = do
  src <- srcParser
  pure $ CompileOptions { ccSrc = src }

cmdParser :: Parser Command
cmdParser = hsubparser
  (command     "eval"  (info (Eval    <$> evalParser)    $ progDesc "Evaluate a compiled SKM program")
    <> command "build" (info (Compile <$> compileParser) $ progDesc "Compiles a CoC program to an SKM program")
    <> command "prove" (info (Prove   <$> proveParser)   $ progDesc "Prove properties of a compiled SKM program, generating a Lean proof definition."))

readExpr :: String -> MaybeT IO Expr
readExpr fname = do
  cts <- liftIO $ T.readFile fname
  case parse pExpr fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right e  ->
      pure e

readExprCoc :: String -> MaybeT IO CocAst.ReadableExpr
readExprCoc fname = do
  cts <- liftIO $ T.readFile fname
  case parse CocP.pProg fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right (stmts, body)  ->
      let stmts' = foldl inlineAll [] stmts in do
        pure $ CocP.inlineDefs stmts' body
  where inlineAll stmts (CocAst.Def id e) =
          let e' = CocP.inlineDefs stmts e in
            (CocAst.Def id e') : stmts

doMain :: MaybeT IO ()
doMain = do
  cfg <- liftIO $ execParser (info (cmdParser <**> helper) $ progDesc "Tools for building SKM applications.")

  case cfg of
    Eval (EvalOptions { eNSteps = n, eSrc = src, lc = lc }) -> do
      e <- if lc then do
            inlined <- readExprCoc src
            fromE <-  (hoistMaybe . CocAst.parseReadableExpr) inlined
            sk    <- (hoistMaybe . ((pure . CocT.opt) <=< CocT.toSk) . CocT.lift) fromE
            pure sk
        else readExpr src
      liftIO $ putStrLn (show (case n of
                         Just n ->
                           eval_n n e
                         Nothing ->
                           eval e))
    Prove (BetaEq BetaEqOptions { bFromSrc = fromSrc }) -> do
      fromE <- readExpr fromSrc

      ((liftIO <$> putStrLn) . Proof.serialize . snd . Proof.cc) fromE
    Compile (CompileOptions { ccSrc = src }) -> do
      fromE <- (readExprCoc src) >>= (hoistMaybe . CocAst.parseReadableExpr)
      sk    <- (hoistMaybe . ((pure . CocT.opt) <=< CocT.toSk) . CocT.lift) fromE

      ((liftIO <$> putStrLn) . show) sk
    _ -> pure ()

main :: IO ()
main = runMaybeT doMain >> (pure ())
