module Main where

import Skm.Ast
import Skm.Parse
import Skm.Eval

data EvalOptions = EvalOptions
  { n_steps        :: (Maybe Int)
  , src            :: String
  }

data BetaEqOptions = BetaEqOptions
  { fromESrc :: String
  , toESrc   :: String
  }

data CompileOptions = CompileOptions
  { src :: String }

data ProveCommand = BetaEq BetaEqOptions

data Command = Eval EvalOptions
  | Prove ProveCommand

nStepsParser :: Parser (Maybe Int)
nStepsParser = optional $ intOption (
  long "n_steps"
  <> short "n"
  <> help "Limit execution to a specific number of steps.")

srcParser :: Parser String
srcParser = argument str (metavar "FILE")

evalParser :: Parser EvalOptions
evalParser = do
  let src <- srcParser
  let n <- nStepsParser

  pure $ EvalOptions { src = src
                     , nSteps = n
                     }

betaEqParser :: Parser BetaEqOptions
betaEqParser = do
  let fromSrc <- srcParser
  let toSrc   <- srcParser

  pure $ BetaEqOptions { fromESrc = fromSrc
                       , toESrc = toSrc
                       }

proveParser :: Parser ProveCommand
proveParser = hsubparser
  ( command "beta_eq"  (info evalParser  $ progDesc "Evaluate a compiled SKM program"))

cmdParser :: Parser Command
cmdParser = hsubparser
  ( command "eval"  (info (Eval  <$> evalParser)  $ progDesc "Evaluate a compiled SKM program")
 <> command "prove" (info (Prove <$> proveParser) $ progDesc "Prove properties of a compiled SKM program, generating a Lean proof definition."))

main :: IO ()
main = do
  cfg <- execParser (info ops $ progDesc "Tools for building SKM applications")

  case cfg of
    Eval cfg -> pure ()
    _ -> pure ()
