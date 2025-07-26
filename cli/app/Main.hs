{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ApplicativeDo              #-}

module Main where

import Control.Monad.Trans.Maybe
import Control.Monad.IO.Class
import System.IO (hPutStrLn, stderr)
import System.Exit (exitWith, ExitCode(ExitFailure))
import Skm.Ast
import Skm.Eval
import Skm.Parse (pExpr)
import Options.Applicative
import qualified Data.Text.IO as T
import Text.Megaparsec (parse, errorBundlePretty)

data EvalOptions = EvalOptions
  { eNSteps :: (Maybe Int)
  , eSrc    :: String
  }

data BetaEqOptions = BetaEqOptions
  { bFromSrc :: String
  , bToSrc   :: String
  }

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

evalParser :: Parser EvalOptions
evalParser = do
  src <- srcParser
  n   <- nStepsParser

  pure $ EvalOptions { eSrc    = src
                     , eNSteps = n
                     }

betaEqParser :: Parser BetaEqOptions
betaEqParser = do
  fromSrc <- srcParser
  toSrc   <- srcParser

  pure $ BetaEqOptions { bFromSrc = fromSrc
                       , bToSrc   = toSrc
                       }

proveParser :: Parser ProveCommand
proveParser = hsubparser
  ( command "beta_eq" (info (BetaEq <$> betaEqParser) $ progDesc "Evaluate a compiled SKM program"))

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

doMain :: MaybeT IO ()
doMain = do
  cfg <- liftIO $ execParser (info (cmdParser <**> helper) $ progDesc "Tools for building SKM applications.")

  case cfg of
    Eval (EvalOptions { eNSteps = n, eSrc = src }) -> do
      e <- readExpr src
      liftIO $ putStrLn (show (case n of
                         Just n ->
                           eval_n n e
                         Nothing ->
                           eval e))
    Prove (BetaEq BetaEqOptions { bFromSrc = fromSrc, bToSrc = toSrc }) -> do
      fromE <- readExpr fromSrc
      toE   <- readExpr toSrc

      pure ()
    _ -> pure ()

main :: IO ()
main = runMaybeT doMain >> (pure ())
