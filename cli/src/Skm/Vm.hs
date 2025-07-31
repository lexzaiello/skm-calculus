module Skm.Vm where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Control.Monad.Trans.Maybe
import Control.Monad.State.Lazy
import Skm.Ast (SkExpr(..))
import Skm.Eval (EvalConfig, EvalConfig(..), tK, tM, tS, tOut)

-- One-step evaluation valid reductions
-- Not defined for left-side evaluation
data Step = KCall
  | SCall
  | MCall
  | Ms
  | Mk
  | Mm
  deriving (Show)

{- Used for logging. We can generate a trace
   which can be used for generating a proof
   These are all valid beta-reduction steps
   taken from the Ast3.lean file

   Right side evaluation should never happen
   Evaluation is left side only

   The left constructor only executes correctly
   when two expressions are on the stack:
   - First expression is the expression the left hand side is equal to
   - Second expression is the right hand side (ideally, this should be unchanged)
   - This will put a Call expression to the stack
-}

data Op = Lhs
  -- For normal forms
  | Rfl SkExpr
  | Memoize
  | Dup
  -- Attempts to parse out an expression into a form recognizable by eval once
  -- Will also push an EvalOnce call if it can parse
  | TryStep
  | EvalOnce Step
  deriving (Show)

type Trace    = [Op]
type Stack    = [Op]
type Register = [SkExpr]
type Cache    = HashMap SkExpr SkExpr

data ExecState = ExecState
  { trace    :: Trace
  , stack    :: Stack
  , register :: Register
  , cache    :: Cache }
  deriving (Show)

data ExecError = ExecError
  { offendingOp :: Maybe Op
  , stackTrace  :: ExecState
  }
  deriving (Show)

memoize :: SkExpr -> SkExpr -> State ExecState ()
memoize fromE toE = modify insert
  where insert (ExecState { trace = t, stack = s, register = r, cache = c }) =
          ExecState { trace = t, stack = s, register = r, cache = HM.insert fromE toE c }

tryMemo :: SkExpr -> State ExecState (Maybe SkExpr)
tryMemo e = gets $ HM.lookup e . cache

push :: Op -> State ExecState ()
push = modify . add
  where add op (ExecState { trace = t, stack = s, register = r, cache = c }) =
          ExecState { trace = t, stack = op:s, register = r, cache = c }

pushE :: SkExpr -> State ExecState ()
pushE = modify . add
  where add e (ExecState { trace = t, stack = s, register = r, cache = c }) =
          ExecState { trace = t, stack = s, register = e:r, cache = c }

pop :: MaybeT (State ExecState) Op
pop = (MaybeT . state) $ \st ->
  case stack st of
    (x:xs) -> (Just x, st { stack = xs, trace = x:trace st })
    []     -> (Nothing, st)

popE :: MaybeT (State ExecState) SkExpr
popE = (MaybeT . state) $ \st ->
  case register st of
    (x:xs) -> (Just x, st { register = xs })
    []     -> (Nothing, st)

pushMany :: [Op] -> State ExecState ()
pushMany = mapM_ push

mkState :: SkExpr -> ExecState
mkState e = snd $ runState (do
    pushMany [TryStep, Rfl e]
  ) $ ExecState { trace = [], stack = [], register = [], cache = HM.fromList [] }

advance :: EvalConfig -> MaybeT (State ExecState) ()
advance cfg = do
  o <- pop

  case o of
    Memoize -> do
      fromE <- popE
      toE   <- popE

      lift $ memoize fromE toE
    Lhs -> do
      lhs <- popE
      rhs <- popE

      (lift . pushMany) $ [Rfl (Call lhs rhs)]
    Rfl e -> (lift . pushE) e
    EvalOnce KCall -> do
      x <- popE

      (lift . pushMany) [TryStep, Rfl x]
    EvalOnce SCall -> do
      x <- popE
      y <- popE
      z <- popE

      (lift . pushMany) [TryStep, Rfl (Call (Call x z) (Call y z))]
    EvalOnce MCall -> do
      lhs <- popE
      rhs <- popE

      (lift . pushMany) [TryStep, Rfl (Call (Call (Call M lhs) rhs) (tOut cfg))]
    EvalOnce Mk ->
      (lift . push) $ Rfl (tK cfg)
    EvalOnce Ms ->
      (lift . push) $ Rfl (tS cfg)
    EvalOnce Mm ->
      (lift . push) $ Rfl (tM cfg)
    Dup -> do
      e <- popE

      (lift . pushMany) [Rfl e, Rfl e]
    TryStep -> do
      e       <- popE
      maybeE' <- (lift . tryMemo) e

      case maybeE' of
        Just e' ->
          (lift . push) $ Rfl e'
        Nothing -> do
          ops <- (case e of
            (Call (Call K x) y) -> (pure [EvalOnce KCall, Rfl x])
            (Call (Call (Call S x) y) z) -> (pure [EvalOnce SCall, Rfl x, Rfl y, Rfl z])
            (Call M K) -> (pure [EvalOnce Mk])
            (Call M M) -> (pure [EvalOnce Mm])
            (Call M S) -> (pure [EvalOnce Ms])
            (Call M (Call lhs rhs)) -> (pure [EvalOnce MCall, Rfl lhs, Rfl rhs])
            (Call lhs rhs) -> (do
              lhs' <- (lift . tryMemo) lhs

              case lhs' of
                Just lhs' ->
                  pure [TryStep, Memoize, Rfl e, Dup, Lhs, Rfl lhs, Rfl rhs]
                Nothing ->
                  pure [TryStep, Memoize, Rfl e, Dup, Lhs, TryStep, Rfl lhs, Rfl rhs])
            x -> (pure [Rfl x]))

          (lift . pushMany) ([Memoize, Rfl e, Dup] ++ ops)

-- There should be only a single expression in the register at the end of execution
outE :: ExecState -> Maybe SkExpr
outE s = case register s of
  [e] -> Just e
  _   -> Nothing

advanceN :: EvalConfig -> Int -> MaybeT (State ExecState) ()
advanceN cfg n
  | n <= 0 = pure ()
  | otherwise = advance cfg >> advanceN cfg (n - 1)

advanceToEnd :: EvalConfig -> ExecState -> Either ExecError ExecState
advanceToEnd cfg state = case stack state of
  op:ops ->
    case (runState . runMaybeT) (advance cfg) state of
      (Just _, state')  -> advanceToEnd cfg state'
      (Nothing, state') -> Left $ ExecError { offendingOp = Just op, stackTrace = state' }
  _ -> Right state

{- Sample execution:
   (((K K) K) (K K)) = (K (K K))

   1. Stack is initialized with `Rfl (((K K) K) (K K))` and `Step` instructions
      - `Rfl expr` puts `expr` in the register
      - Register is a stack for only expressions
   2. `Step` hit during advance, and the original expression is found by popRfl
   3. Attempt to run one-step evaluation of the expression. This puts nothing on the stack,
      since no evaluation is possible. Nothing is returned by eval function, so we descend
      by pushing the left hand side and right hand side to the stack, then the `Step` opcode
      to advance the `Lhs` in this order:
        - `Lhs`
        - `Rfl` right hand side expr
        - `Rfl` left hand side expr
        - `Step`
   4. We hit the `Step` opcode, so we run the K evaluation function for the left hand side.
      It succeeds.
   5. `Rfl` puts the left hand side expression in the register
   6. `Rfl` puts the right hand side expression in the reigster
   7. `Left` creates a Call expression with the left hand side and right hand side popped
      from the register, and pushes `Rfl (Call lhs rhs)` in the stack
   8. How do we know if a program is done?
      - Memoize the register. If we ever encounter the same register twice, we are cooked.
-}

eval :: EvalConfig -> SkExpr -> Either ExecError (Maybe SkExpr)
eval cfg e = outE <$> advanceToEnd cfg s0
  where s0 = mkState e

evalN :: EvalConfig -> Int -> SkExpr -> Either ExecError SkExpr
evalN cfg n e = case (runState . runMaybeT) (advanceN cfg n) s0 of
  (Just _, state')  -> maybe (Left $ log state') Right (outE state')
  (Nothing, state') -> Left $ log state'
  where s0   = mkState e
        log s = ExecError { offendingOp = (case trace s of
                                             op:_ -> Just op
                                             _ -> Nothing)
                          , stackTrace = s }
