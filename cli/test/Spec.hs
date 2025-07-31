{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Applicative ((<|>))
import Data.Text (Text)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import Test.Hspec
import Skm.Eval (EvalConfig)
import Skm.Vm (eval)
import Skm (Error(..))
import Skm.Compiler.Ast (CompilationError(..))
import Skm.Cli.Exec (getEvalConfig, getStreamRawPath, parseExprCoc, ccRawCocToSk)
import Skm.Cli.OptParse (RawPath)

primitivesSrc :: RawPath
primitivesSrc = "../std/PrimitiveTypes.skm"

primitivesSrcBackup :: RawPath
primitivesSrcBackup = "std/PrimitiveTypes.skm"

type TestM = ExceptT String IO

type RawExpr = Text

stringifyErr :: Show a => Either a out -> Either String out
stringifyErr = either (Left . show) Right

runRawE :: EvalConfig -> RawExpr -> Either Error (Maybe String)
runRawE cfg s = do
  parsed <- either (Left . CompError . ParseFailure) Right $ parseExprCoc "" s
  skE   <- either (Left . CompError) Right $ ccRawCocToSk parsed

  e' <- either (Left . ExecutionError) Right $ eval cfg skE

  pure $ (show <$> e')

doTest :: TestM () -> IO ()
doTest m = do
  res <- runExceptT m
  case res of
    Left err -> expectationFailure . show $ err
    Right () -> pure ()

getCfg :: TestM EvalConfig
getCfg = do
  stdStream <- liftIO $ (getStreamRawPath primitivesSrc) <|> (getStreamRawPath primitivesSrcBackup)
  ExceptT $ fmap stringifyErr (pure $ getEvalConfig primitivesSrc stdStream)

testExprEval :: RawExpr -> Maybe String -> TestM ()
testExprEval input expected = do
  cfg <- ExceptT $ fmap stringifyErr (runExceptT getCfg)
  res <- ExceptT . pure . stringifyErr $ runRawE cfg input
  liftIO $ res `shouldBe` (expected)
  pure ()

main :: IO ()
main = hspec $ do
  describe "SKM E2E tests" $ do
    it "compiles and evaluates identity function correctly" $ doTest (testExprEval "((\\x => x) K)" (Just "K"))
    it "compiles and evaluates a boolean correctly" $ doTest $ do
      testExprEval "((\\a b => a) K S)" (Just "K")
      testExprEval "((\\a b => b) K S)" (Just "S")
      testExprEval "((\\a b c => c) K K S)" (Just "S")
