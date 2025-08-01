{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Applicative ((<|>))
import Data.Text (Text)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import Test.Hspec
import Skm.Eval (EvalConfig, ReductionMode(..))
import Skm.Vm (eval)
import Skm (Error(..))
import Skm.Compiler.Ast (CompilationError(..))
import Skm.Cli.Exec (getEvalConfig, getStreamRawPath, parseExprCoc, ccRawCocToSk)
import Skm.Cli.OptParse (RawPath)

-- TODO: Better way to do this with Nix
primitives :: Text
primitives = "def arrow := λ a b f => ((f a) b)\ndef t_in  := λ a b => a\ndef t_out := λ a b => b\ndef t_k   := λ a => (arrow (M a) (λ b => (arrow (M b) (M a))))\ndef t_s   := λ x => (arrow (M x) (λ y => (arrow (M y) (λ z => (arrow (M z) (M ((x z) (y z))))))))\ndef t_m   := λ e => (arrow (M e) (M (M e)))\ndef t_i   := λ e => (arrow (M e) (M e))"

type TestM = ExceptT String IO

type RawExpr = Text

stringifyErr :: Show a => Either a out -> Either String out
stringifyErr = either (Left . show) Right

runRawE :: EvalConfig -> RawExpr -> Either Error String
runRawE cfg s = do
  parsed <- either (Left . CompError . ParseFailure) Right $ parseExprCoc "" s
  skE   <- either (Left . CompError) Right $ ccRawCocToSk parsed

  e' <- either (Left . ExecutionError) Right $ eval cfg skE

  pure $ show e'

doTest :: TestM () -> IO ()
doTest m = do
  res <- runExceptT m
  case res of
    Left err -> expectationFailure . show $ err
    Right () -> pure ()

getCfg :: TestM EvalConfig
getCfg = do
  let stdStream = primitives
  ExceptT $ fmap stringifyErr (pure $ getEvalConfig Lazy "" stdStream)

testExprEval :: RawExpr -> String -> TestM ()
testExprEval input expected = do
  cfg <- ExceptT $ fmap stringifyErr (runExceptT getCfg)
  res <- ExceptT . pure . stringifyErr $ runRawE cfg input
  liftIO $ res `shouldBe` expected
  pure ()

main :: IO ()
main = hspec $ do
  describe "SKM E2E tests" $ do
    it "compiles and evaluates identity function correctly" $ doTest (testExprEval "((\\x => x) K)" "K")
    it "compiles and evaluates a boolean correctly" $ doTest $ do
      testExprEval "((\\a b => a) K S)" "K"
      testExprEval "((\\a b => b) K S)" "S"
      testExprEval "((\\a b c => c) K K S)" "S"
