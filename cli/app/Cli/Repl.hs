module Cli.Repl where

promptPs :: String
promptPs = ">> "

streamStdinName :: String
streamStdinName = "<STDIN>"

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
      sk <- (hoistMaybe . ((pure . CocT.opt) <=< CocT.toSk <=< CocT.lift)) e

      pure sk
    ReplOptions { rLc = False } ->
      parseSkStream streamStdinName rawE

  let e' = eval eCfg e
  printEval e'

  repl eCfg opt
