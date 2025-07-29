{-# LANGUAGE DuplicateRecordFields #-}

module Cli.OptParse where

import Skm.Eval (EvalConfig)
import Cli.Exec (readCocSrc, flattenDef)

type RawPath = String

parseRawPathArg :: Parser RawPath
parseRawPathArg = argument str (metavar "FILE"
                               <> help "The source file path.")

primitivesSrc :: RawPath
primitivesSrc = "std/PrimitiveTypes.skm"

data StepCount = StepCount Int

parseNSteps :: Parser StepCount
parseNSteps = option auto (long "n_steps"
                           <> short 'n'
                           <> help "Limit execution to a specific number of steps.")

-- Some commands can be run in pure SKM or lambda calculus (comp to SKM) mode
type LambdaExecConfig = EvalConfig

parseLambdaExecConfig :: Parser LambdaExecConfig
parseLambdaExecConfig = do
  pathStd <- (fromMaybe primitivesSrc . optional) $
      option auto (long "std_src"
                   <> help "Sets a custom path to the standard library. Should be a directory."
                   <> metavar "PATH")

    -- We bootstrap the definitions of M x from the standard library
    -- Todo: exception handling
    (stmts, _) <- readCocSrc pathStd

    tIn   <- flattenDef "t_in"  stmts
    tOut  <- flattenDef "t_out" stmts
    arrow <- flattenDef "arrow" stmts
    tK    <- flattenDef "t_k"   stmts
    tS    <- flattenDef "t_s"   stmts
    tM    <- flattenDef "t_m"   stmts

    pure $ EvalConfig
      { tIn  = tIn
      , tOut = tIn
      , arrow = arrow
      , tK = tK
      , tS = tS
      , tM = tM
      }

data EvalOptions = EvalOptions {
  nSteps  :: Maybe StepCount
  , lcCfg :: Maybe LambdaExecConfig
  , src   :: RawPath }

parseEvalOptions :: Parser EvalOptions
parseEvalOptions = do
  n      <- optional parseNsteps
  cfg    <- optional parseLambdaExecConfig
  srcPat <- parseRawPathArg

  pure $ EvalOption { nSteps = n
                    , lcCfg = cfg
                    , src = srcPat }

-- Dry mode puts all SK compilations inline, retaining definition names
data CompileOptions = CompileOptions
  { dry   :: Bool
  , src   :: RawPath }

parseCompileOptions :: Parser CompileOptions
parseCompileOptions = do
  isDry <- (fromMaybe False . optional)
    $ switch (long "dry"
              <> short 'd'
              <> help "Compile lambda expressions inline to SK.")
  src <- parseRawPathArg

  pure $ CompileOptions { dry = isDry }

instance WithParser CompileOptions where
  parser = do
    isDry <- (fromMaybe False . optional) $ switch (long "dry"
                                <> short 'd'
                                <> help "Compile lambda expressions inline to SK.")

    pure $ CompileOptions { dry = isDry }

data ProveCommand = BetaEq RawPath

parseProveCommand :: Parser ProveCommand
parseProveCommand = hsubparser $
    command "beta_reduce" (info (BetaEq <$> parseRawPathArg) $ progDesc "Generate a proof of valid beta-reduction of an expression.")

data Command = Eval EvalOptions
  | Prove ProveCommand
  | Compile CompileOptions
  | Repl (Maybe LambdaExecConfig)

cmdParser :: Parser Command
cmdParser = hsubparser
  (command     "eval"  (info (Eval    <$> parseEvalOptions)                  $ progDesc "Evaluate a compiled SKM program.")
    <> command "build" (info (Compile <$> parseCompileOptions)               $ progDesc "Compiles a CoC program to an SKM program.")
    <> command "prove" (info (Prove   <$> parseProveCommand)                 $ progDesc "Prove properties of a compiled SKM program, generating a Lean proof definition.")
    <> command "repl"  (info (Repl    <$> optional parseLambdaExecConfig)    $ progDesc "Launch an interactive SKM session."))

readCommand :: IO Command
readCommand = execParser $ info (cmdParser <**> helper) $ (progDesc "Tools for building SKM applications.")
