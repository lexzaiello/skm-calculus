module Skm
  ( module Skm.Ast
  , module Skm.Eval
  , module Skm.Parse
  ) where

import Text.Printf (printf)
import Skm.Ast
import Skm.Eval
import Skm.Parse
import Skm.Compiler.Ast (CompilationError)
import Skm.Vm (ExecError)

data Error = CompError CompilationError
  | ExecutionError ExecError

instance Show for Error where
  show (CompError err) = printf "compilation encountered an error: %s" (show err)
  show (ExecError err) = printf "execution encountered an error: %s"   (show err)

ccResultToGenResult :: CompilationResult a -> Except Error a
ccResultToGenResult = either (Left CompError) Right

execResultToGenResult :: Either ExecError a -> Except Error a
execResultToGenResult = either (Left ExecutionError) Right
