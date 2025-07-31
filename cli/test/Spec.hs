module Spec where

import Control.Monad.Trans.Except
import Data.Either (either)
import Test.Hspec
import Skm.Eval (EvalConfig)
import Skm.Vm (eval)
import Skm (Error(..), ccResultToGenResult)
import Cli.Exec (getStreamRawPath, parseExprCoc, ccRawCocToSk)
import Cli.OptParse (primitivesSrc)

type RawExpr = String

runRawE :: EvalConfig -> RawExpr -> Either Error RawExpr
runRawE cfg s = do
  parsed <- either (Left . CompilationError . ParseFailure) Right $ parseExprCoc "" s
  skE   <- either (Left . CompilationError) Right $ ccRawCocToSk parsed

  e' <- either (Left . ExecutionError) Right $ eval cfg skE

  pure (show e')

doTest :: TestM () -> IO ()
doTest m = do
  res <- runExceptT m
  case res of
    Left err -> expectationFailure err
    Right () -> pure ()

getCfg :: ExceptT Error (IO EvalConfig)
getCfg = do
  stdStream <- liftIO $ getStreamRawPath primitivesSrc
  (ExceptT . pure . ccResultToGenResult) $ getEvalConfig stdPath stdStream

testIdentity :: TestM ()
testIdentity = do
  let input = "((\\x => x) K)"
  res <- runRawE
  res `shouldBe` "K"

main :: IO ()
main = hspec $ do
  describe "SKM E2E tests" $ do
    it "compiles and evaluates identity function correctly" $ runTest testIdentity
