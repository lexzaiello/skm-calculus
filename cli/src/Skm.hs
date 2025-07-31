module Skm where

import Text.Printf (printf)
import Skm.Compiler.Ast (CompilationError, CompilationResult)
import Skm.Vm (ExecError)

data Error = CompError !CompilationError
  | ExecutionError !ExecError

instance Show Error where
  show (CompError err)      = printf "compilation encountered an error: %s" (show err)
  show (ExecutionError err) = printf "execution encountered an error: %s"   (show err)

ccResultToGenResult :: CompilationResult a -> Either Error a
ccResultToGenResult = either (Left . CompError) Right

execResultToGenResult :: Either ExecError a -> Either Error a
execResultToGenResult = either (Left . ExecutionError) Right
