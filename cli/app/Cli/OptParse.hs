{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ApplicativeDo #-}

module Cli.OptParse where

import Data.Maybe (fromMaybe)
import Options.Applicative

type RawPath = String

parseRawPathArg :: Parser RawPath
parseRawPathArg = argument str (metavar "FILE"
                               <> help "The source file path.")

primitivesSrc :: RawPath
primitivesSrc = "std/PrimitiveTypes.skm"

type StepCount = Int

parseNSteps :: Parser StepCount
parseNSteps = option auto (long "n_steps"
                           <> short 'n'
                           <> help "Limit execution to a specific number of steps.")

-- Some commands can be run in pure SKM or lambda calculus (comp to SKM) mode
newtype LambdaExecConfig = LambdaExecConfig { stdPath :: RawPath }

parseLambdaExecConfig :: Parser LambdaExecConfig
parseLambdaExecConfig = do
  pathStd <- optional $
      option auto (long "std_src"
                   <> help "Sets a custom path to the standard library. Should be a directory."
                   <> metavar "PATH")

  pure $ LambdaExecConfig
    { stdPath = fromMaybe primitivesSrc pathStd }

data EvalOptions = EvalOptions {
  nSteps  :: !(Maybe StepCount)
  , lcCfg :: !(Maybe LambdaExecConfig)
  , src   :: !RawPath }

parseEvalOptions :: Parser EvalOptions
parseEvalOptions = do
  n      <- optional parseNSteps
  cfg    <- optional parseLambdaExecConfig
  srcPat <- parseRawPathArg

  pure $ EvalOptions { nSteps = n
                     , lcCfg = cfg
                     , src = srcPat }

-- Dry mode puts all SK compilations inline, retaining definition names
data CompileOptions = CompileOptions
  { dry   :: !Bool
  , src   :: !RawPath }

parseCompileOptions :: Parser CompileOptions
parseCompileOptions = do
  isDry <- optional
    $ switch (long "dry"
              <> short 'd'
              <> help "Compile lambda expressions inline to SK.")
  source <- parseRawPathArg

  pure $ CompileOptions { dry = fromMaybe False isDry, src = source }

newtype ProveCommand = BetaEq RawPath

parseProveCommand :: Parser ProveCommand
parseProveCommand = hsubparser $
    command "beta_reduce" (info (BetaEq <$> parseRawPathArg) $ progDesc "Generate a proof of valid beta-reduction of an expression.")

data Command = Eval !EvalOptions
  | Prove !ProveCommand
  | Compile !CompileOptions
  | Repl !(Maybe LambdaExecConfig)

cmdParser :: Parser Command
cmdParser = hsubparser
  (command     "eval"  (info (Eval    <$> parseEvalOptions)                  $ progDesc "Evaluate a compiled SKM program.")
    <> command "build" (info (Compile <$> parseCompileOptions)               $ progDesc "Compiles a CoC program to an SKM program.")
    <> command "prove" (info (Prove   <$> parseProveCommand)                 $ progDesc "Prove properties of a compiled SKM program, generating a Lean proof definition.")
    <> command "repl"  (info (Repl    <$> optional parseLambdaExecConfig)    $ progDesc "Launch an interactive SKM session."))

readCommand :: IO Command
readCommand = execParser $ info (cmdParser <**> helper) $ progDesc "Tools for building SKM applications."
