{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ApplicativeDo #-}

module Skm.Cli.OptParse where

import Skm.Eval (ReductionMode(..))
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

newtype ExecConfig = ExecConfig { stdPath :: RawPath }

parseExecConfig :: Parser ExecConfig
parseExecConfig = do
  pathStd <- optional $
      option auto (long "std_src"
                   <> help "Sets a custom path to the standard library. Should be a directory."
                   <> metavar "PATH")

  pure $ ExecConfig
    { stdPath = fromMaybe primitivesSrc pathStd }

data EvalMode = Lc
  | Raw

parseReductionMode :: Parser ReductionMode
parseReductionMode = flag Lazy Strict $ long "strict" <> help "Uses the call-by-value reduction strategy."

parseEvalMode :: Parser EvalMode
parseEvalMode = flag Raw Lc $ long "lc" <> help "Precompiles lambda calculus to SKM before evaluation."

data EvalOptions = EvalOptions {
  nSteps    :: !(Maybe StepCount)
  , execCfg :: !ExecConfig
  , mode    :: !EvalMode
  , src     :: !RawPath
  , redMode :: !ReductionMode }

parseEvalOptions :: Parser EvalOptions
parseEvalOptions = do
  n      <- optional parseNSteps
  cfg    <- parseExecConfig
  isLc   <- parseEvalMode
  redMod <- parseReductionMode
  srcPat <- parseRawPathArg

  pure $ EvalOptions { nSteps  = n
                     , execCfg = cfg
                     , mode    = isLc
                     , src = srcPat
                     , redMode = redMod }

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

newtype ProveCommand = BetaEq EvalOptions

parseProveCommand :: Parser ProveCommand
parseProveCommand = hsubparser $
    command "beta_reduce" (info (BetaEq <$> parseEvalOptions) $ progDesc "Generate a proof of valid beta-reduction of an expression.")

data ReplOptions = ReplOptions
  { mode    :: !EvalMode
  , execCfg :: !ExecConfig
  , redMode :: !ReductionMode
  }

parseReplCommand :: Parser ReplOptions
parseReplCommand = do
  cfg    <- parseExecConfig
  isLc   <- parseEvalMode
  redMod <- parseReductionMode

  pure $ ReplOptions { mode    = isLc
                     , execCfg = cfg
                     , redMode = redMod }

data Command = Eval !EvalOptions
  | Prove !ProveCommand
  | Compile !CompileOptions
  | Repl !ReplOptions

cmdParser :: Parser Command
cmdParser = hsubparser
  (command     "eval"  (info (Eval    <$> parseEvalOptions)    $ progDesc "Evaluate a compiled SKM program.")
    <> command "build" (info (Compile <$> parseCompileOptions) $ progDesc "Compiles a CoC program to an SKM program.")
    <> command "prove" (info (Prove   <$> parseProveCommand)   $ progDesc "Prove properties of a compiled SKM program, generating a Lean proof definition.")
    <> command "repl"  (info (Repl    <$> parseReplCommand)    $ progDesc "Launch an interactive SKM session."))

readCommand :: IO Command
readCommand = execParser $ info (cmdParser <**> helper) $ progDesc "Tools for building SKM applications."
