{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ApplicativeDo              #-}

module Main where

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

cmdParser :: Parser Command
cmdParser = hsubparser
  ( command "eval"  (info (Eval  <$> evalParser)  $ progDesc "Evaluate a compiled SKM program")
 <> command "prove" (info (Prove <$> proveParser) $ progDesc "Prove properties of a compiled SKM program, generating a Lean proof definition."))

main :: IO ()
main = do
  cfg <- execParser (info (cmdParser <**> helper) $ progDesc "Tools for building SKM applications.")

  case cfg of
    Eval (EvalOptions { eNSteps = n, eSrc = src }) -> do
      cts <- T.readFile src
      case parse pExpr src cts of
        Left err -> putStr (errorBundlePretty err)
        Right e  -> putStrLn (show e)
    _ -> pure ()
