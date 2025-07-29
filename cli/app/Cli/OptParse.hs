module Cli.OptParse where

primitivesSrc :: String
primitivesSrc = "std/PrimitiveTypes.skm"

data EvalOptions = EvalOptions
  { eNSteps :: (Maybe Int)
  , eSrc    :: String
  , lc      :: Bool
  }

data BetaEqOptions = BetaEqOptions
  { bFromSrc :: String }

data CompileOptions = CompileOptions
  { ccSrc :: String
  , dry   :: Bool}

data ReplOptions = ReplOptions
  { rLc :: Bool }

data ProveCommand = BetaEq BetaEqOptions

data Command = Eval EvalOptions
  | Prove ProveCommand
  | Compile CompileOptions
  | Repl ReplOptions

nStepsParser :: Parser (Maybe Int)
nStepsParser = optional $ option auto (
  long "n_steps"
  <> short 'n'
  <> help "Limit execution to a specific number of steps.")

srcParser :: Parser String
srcParser = argument str (metavar "FILE")

lcParser :: Parser (Maybe Bool)
lcParser = optional $ switch (long "lc" <> short 'l' <> help "Compile lambda calculus and evaluate as SKM.")

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

replParser :: Parser ReplOptions
replParser = do
  isLc <- lcParser

  pure $ ReplOptions { rLc = fromMaybe False isLc }

proveParser :: Parser ProveCommand
proveParser = hsubparser
  (command "beta_reduce" (info (BetaEq <$> betaEqParser) $ progDesc "Generate a proof of valid beta-reduction of an expression."))

compileParser :: Parser CompileOptions
compileParser = do
  src <- srcParser
  dry <- optional $ switch (long "dry" <> short 'd' <> help "Compile lambda expressions inline to SK.")
  pure $ CompileOptions { ccSrc = src, dry = fromMaybe False dry }

cmdParser :: Parser Command
cmdParser = hsubparser
  (command     "eval"  (info (Eval    <$> evalParser)    $ progDesc "Evaluate a compiled SKM program.")
    <> command "build" (info (Compile <$> compileParser) $ progDesc "Compiles a CoC program to an SKM program.")
    <> command "prove" (info (Prove   <$> proveParser)   $ progDesc "Prove properties of a compiled SKM program, generating a Lean proof definition.")
    <> command "repl"  (info (Repl    <$> replParser)    $ progDesc "Launch an interactive SKM session."))

readCommand :: IO Command
readCommand = execParser (info (cmdParser <**> helper) $ progDesc "Tools for building SKM applications.")

readEvalConfig :: MaybeT IO EvalConfig
readEvalConfig = do
  (stmts, _) <- readProgCoc primitivesSrc

  tIn   <- (flatten . unwrapCompError) $ findDef "t_in"  stmts >>= unwrapCompError
  tOut  <- (flatten . unwrapCompError) $ findDef "t_out" stmts >>= unwrapCompError
  arrow <- (flatten . unwrapCompError) $ findDef "arrow" stmts >>= unwrapCompError
  tK    <- (flatten . unwrapCompError) $ findDef "t_k"   stmts >>= unwrapCompError
  tS    <- (flatten . unwrapCompError) $ findDef "t_s"   stmts >>= unwrapCompError
  tM    <- (flatten . unwrapCompError) $ findDef "t_m"   stmts >>= unwrapCompError

  pure $ EvalConfig { tIn  = tIn
             , tOut = tIn
             , arrow = arrow
             , tK = tK
             , tS = tS
             , tM = tM
             }
  where flatten = MaybeT . fmap join . runMaybeT
