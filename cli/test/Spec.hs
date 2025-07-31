module Spec where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import Data.Either (either)
import Test.Hspec
import Skm.Eval (EvalConfig)
import Skm.Vm (eval)
import Skm (Error(..), ccResultToGenResult)
import Skm.Compiler.Ast (CompilationError(..))
import Skm.Cli.Exec (getEvalConfig, getStreamRawPath, parseExprCoc, ccRawCocToSk)
import Skm.Cli.OptParse (primitivesSrc)

type TestM = ExceptT Error IO

type RawExpr = String

runRawE :: EvalConfig -> RawExpr -> Either Error RawExpr
runRawE cfg s = do
  parsed <- either (Left . CompError . ParseFailure) Right $ parseExprCoc "" s
  skE   <- either (Left . CompError) Right $ ccRawCocToSk parsed

  e' <- either (Left . ExecutionError) Right $ eval cfg skE

  pure (show e')

doTest :: TestM () -> IO ()
doTest m = do
  res <- runExceptT m
  case res of
    Left err -> expectationFailure err
    Right () -> pure ()

getCfg :: ExceptT Error IO EvalConfig
getCfg = do
  stdStream <- liftIO $ getStreamRawPath primitivesSrc
  (ExceptT . pure . ccResultToGenResult) $ getEvalConfig primitivesSrc stdStream

testIdentity :: TestM ()
testIdentity = do
  let input = "((\\x => x) K)"
  res <- runRawE
  res `shouldBe` "K"

main :: IO ()
main = hspec $ do
  describe "SKM E2E tests" $ do
    it "compiles and evaluates identity function correctly" $ doTest testIdentity
