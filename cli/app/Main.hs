{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ApplicativeDo              #-}

module Main where

import Text.Printf
import Data.List (find)
import Data.Text (Text, pack)
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
  { ccSrc :: String
  , dry   :: Bool}

data ReplOptions = ReplOptions
  { rLc :: Bool }

data ProveCommand = BetaEq BetaEqOptions

data Command = Eval EvalOptions
  | Prove ProveCommand
  | Compile CompileOptions
  | Repl ReplOptions

primitivesSrc :: String
primitivesSrc = "std/PrimitiveTypes.skm"

promptPs :: String
promptPs = ">> "

streamStdinName :: String
streamStdinName = "<STDIN>"

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

readExpr :: String -> MaybeT IO Expr
readExpr fname = do
  cts <- liftIO $ T.readFile fname
  case parse pExpr fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right e  ->
      pure e

type StreamName = String

parseSkStream :: StreamName -> Text -> MaybeT IO Expr
parseSkStream fname cts = do
  case parse pExpr fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right e  ->
      pure e

parseProgCocStream :: StreamName -> Text -> MaybeT IO ([CocAst.Stmt], Maybe CocAst.ReadableExpr)
parseProgCocStream fname cts = do
  case parse CocP.pProg fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right (stmts, body)  ->
      let stmts' = foldl inlineAll [] stmts in do
        pure $ (stmts', CocP.inlineDefs stmts' <$> body)
  where inlineAll stmts (CocAst.Def id e) = (CocAst.Def id (CocP.inlineDefs stmts e)) : stmts

readProgCoc :: String -> MaybeT IO ([CocAst.Stmt], Maybe CocAst.ReadableExpr)
readProgCoc fname = do
  cts <- liftIO $ T.readFile fname
  case parse CocP.pProg fname cts of
    Left err ->
      (liftIO $ hPutStrLn stderr (errorBundlePretty err)) >> empty
    Right (stmts, body)  ->
      let stmts' = foldl inlineAll [] stmts in do
        pure $ (stmts', CocP.inlineDefs stmts' <$> body)
  where inlineAll stmts (CocAst.Def id e) =
          let e' = CocP.inlineDefs stmts e in
            (CocAst.Def id e') : stmts

readExprCoc :: String -> MaybeT IO CocAst.ReadableExpr
readExprCoc fname = do
  (_, maybeE) <- readProgCoc fname
  hoistMaybe maybeE

cc :: CocAst.ReadableExpr -> Maybe Expr
cc = ((pure . CocT.opt) <=< CocT.toSk) . CocT.lift <=< CocAst.parseReadableExpr

ccInline :: CocAst.Stmt -> Maybe CocAst.Stmt
ccInline (CocAst.Def name value) = do
  value' <- ((CocAst.transmuteESk . CocT.lift) <=< CocAst.parseReadableExpr) value

  pure $ CocAst.Def name value'

repl :: EvalConfig -> ReplOptions -> MaybeT IO ()
repl eCfg opt = do
  liftIO $ putStr promptPs
  liftIO $ hFlush stdout
  rawE <- pack <$> (liftIO getLine)

  e <- case opt of
    ReplOptions { rLc = True } -> do
      (stmts, maybeE) <- parseProgCocStream streamStdinName rawE
      rawE <- hoistMaybe maybeE
      e  <- (hoistMaybe . CocAst.parseReadableExpr) rawE
      sk <- (hoistMaybe . ((pure . CocT.opt) <=< CocT.toSk) . CocT.lift) e

      pure sk
    ReplOptions { rLc = False } ->
      parseSkStream streamStdinName rawE

  let e' = eval eCfg e
  liftIO $ putStrLn (show e')

  repl eCfg opt

findDef :: String -> [CocAst.Stmt] -> Maybe Expr
findDef name stmts = (body <$> find matches stmts) >>= cc
  where body    (CocAst.Def _ bdy)   = bdy
        matches (CocAst.Def ident _) = ident == name

readEvalConfig :: MaybeT IO EvalConfig
readEvalConfig = do
  (stmts, _) <- readProgCoc primitivesSrc

  tIn   <- hoistMaybe $ findDef "t_in"  stmts
  tOut  <- hoistMaybe $ findDef "t_out" stmts
  arrow <- hoistMaybe $ findDef "arrow" stmts
  tK    <- hoistMaybe $ findDef "t_k"   stmts
  tS    <- hoistMaybe $ findDef "t_s"   stmts
  tM    <- hoistMaybe $ findDef "t_m"   stmts

  pure $ EvalConfig { tIn  = tIn
             , tOut = tIn
             , arrow = arrow
             , tK = tK
             , tS = tS
             , tM = tM
             }

printEval :: Either ExecError (Maybe Expr) -> IO ()
printEval (Left e) =
  hPutStrLn stderr $ printf "Execution failed. Offending opcode: %s. Backtrace: %s\n" (show $ offendingOp e) (show $ stackTrace e)
printEval (Right (Just e)) = putStrLn (show e)
printEval (Right Nothing)  = putStrLn "execution succeeded, but outputted nothing."

doMain :: MaybeT IO ()
doMain = do
  cfg <- liftIO $ execParser (info (cmdParser <**> helper) $ progDesc "Tools for building SKM applications.")
  prim <- readEvalConfig

  case cfg of
    Eval (EvalOptions { eNSteps = n, eSrc = src, lc = lc }) -> do
      e <- if lc then do
            inlined <- readExprCoc src
            fromE <- (hoistMaybe . CocAst.parseReadableExpr) inlined
            sk    <- (hoistMaybe . ((pure . CocT.opt) <=< CocT.toSk) . CocT.lift) fromE
            pure sk
        else readExpr src
      liftIO $ printEval (case n of
                            Just n ->
                              Just <$> (evalN prim n e)
                            Nothing ->
                              eval prim e)
    Prove (BetaEq BetaEqOptions { bFromSrc = fromSrc }) -> do
      fromE <- readExpr fromSrc

      ((liftIO <$> putStrLn) . Proof.serialize . snd . Proof.cc) fromE
    Compile (CompileOptions { ccSrc = src, dry = dry }) -> do
      if not dry then do
        fromE <- (readExprCoc src) >>= (hoistMaybe . CocAst.parseReadableExpr)
        sk    <- (hoistMaybe . ((pure . CocT.opt) <=< CocT.toSk) . CocT.lift) fromE

        ((liftIO <$> putStrLn) . show) sk
      else (do
        (fromStmts, fromE) <- readProgCoc src
        let fromStmts' = map ccInline fromStmts
        let fromE'     = CocT.lift <$> (fromE >>= CocAst.parseReadableExpr)

        let fmtStmts = (case fromE' of
                             (Just fromE') -> ((show fromE') : (map show $ catMaybes fromStmts'))
                             Nothing       -> (map show) $ catMaybes fromStmts')

        liftIO $ putStrLn (intercalate "\n" fmtStmts))
    Repl opts -> repl prim opts
    _ -> pure ()

main :: IO ()
main = runMaybeT doMain >> (pure ())
