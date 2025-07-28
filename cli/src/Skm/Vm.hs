module Skm.Vm where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Control.Monad.Maybe (runMaybeT)
import Control.Monad.State.Lazy
import Skm.Ast
import Skm.Eval (step, EvalConfig)

-- One-step evaluation valid reductions
-- Not defined for left-side evaluation
data Step = KCall
  | SCall
  | MCall
  | Ms
  | Mk
  | Mm

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
  | Rfl Expr
  | Memoize
  -- Attempts to parse out an expression into a form recognizable by eval once
  -- Will also push an EvalOnce call if it can parse
  | TryStep
  | EvalOnce Step

type Trace    = [Op]
type Stack    = [Op]
type Register = [Expr]
type Cache    = HashMap Expr Expr

data ExecState = ExecState
  { trace    :: Trace
  , stack    :: Stack
  , register :: Register
  , cache    :: Cache }

data ExecError = ExecError
  { offendingOp :: Op
  , stackTrace  :: ExecState
  }

memoize :: Expr -> Expr -> State ExecState ()
memoize = modify . insert
  where insert fromE toE (ExecState { trace = t, stack = s, register = r, cache = c }) =
          ExecState { trace = t, stack = s, register = s, cache = insert fromE toE }

tryMemo :: Expr -> State ExecState (Maybe Expr)
tryMemo e = gets $ (lookup e) . cache

push :: Op -> State ExecState ()
push = modify . add
  where add op (ExecState { trace = t, stack = s, register = r }) =
          ExecState { trace = op:t, stack = op:s, register = r}

pushE :: Expr -> State ExecState ()
pushE = modify . add
  where add e (ExecState { trace = t, stack = s, register = r }) =
          ExecState { trace = t, stack = s, register = e:r }

pop :: MaybeT (State ExecState) Op
pop = do
  op <- gets $ uncons . stack
  modify doPop
  pure op
  where doPop (ExecState { trace = t, stack = x:xs, register = r }) =
          ExecState { trace = t, stack = xs, register = r}

popE :: MaybeT (State ExecState) Expr
popE = do
  e <- gets $ uncons . register
  modify doPop
  pure e
  where doPop (ExecState { trace = t, stack = s, register = x:xs }) =
          ExecState { trace = t, stack = s, register = xs }

pushMany :: [Op] -> State ExecState ()
pushMany = mapM_ push

mkState :: Expr -> ExecState
mkState e = runState (do
    pushMany [TryStep, Rfl e]
  ) $ ExecState { trace = [], stack = [], register = [], cache = [] }

advance :: EvalConfig -> MaybeT (State ExecState) ()
advance cfg = do
  o <- pop

  case o of
    Memoize -> do
      fromE <- popE
      toE   <- popE

      memoize fromE toE
    Lhs -> do
      lhs <- popE
      rhs <- popE

      push $ (Rfl (Call lhs rhs))
    Rfl e -> pushE e
    EvalOnce KCall ->
      x <- popE

      pushMany [Memoize, Rfl (Call (Call K x) y), TryStep, Rfl x]
    EvalOnce SCall ->
      x <- popE
      y <- popE
      z <- popE

      pushMany [ Memoize
               , Rfl (Call (Call (Call S x) y) z)
               , TryStep, Rfl (Call (Call x z) (Call y z))]
    EvalOnce MCall ->
      lhs <- popE
      rhs <- popE

      pushMany [ Memoize
               , Rfl (Call M (lhs rhs))
               , TryStep
               , Rfl (Call (Call (Call M lhs) rhs) (tOut cfg))]
    EvalOnce Mk ->
      push $ Rfl (tK cfg)
    EvalOnce Ms ->
      push $ Rfl (tS cfg)
    EvalOnce Mm ->
      push $ Rfl (tM cfg)
    TryStep ->
      e <- popE

      case tryMemo e of
        Just e' ->
          push $ Rfl e'
      case e of
        (Call (Call K x) y) ->
          pushMany [EvalOnce KCall, Rfl x]
        (Call (Call (Call S x) y) z) ->
          pushMany [EvalOnce SCall, Rfl x, Rfl y, Rfl z]
        (Call M K) ->
          push $ EvalOnce Mk
        (Call M M) ->
          push $ EvalOnce Mm
        (Call M S) ->
          push $ EvalOnce Ms
        (Call M (Call lhs rhs)) ->
          pushMany [EvalOnce MCall, Rfl lhs, Rfl rhs]
        (Call lhs rhs) ->
          pushMany [Memoize, Rfl e, Lhs, TryStep, Rfl lhs, Rfl rhs]
        x -> pushMany[Memoize, Rfl x]

advanceToEnd :: EvalConfig -> ExecState -> Either ExecError ExecState
advanceToEnd cfg state = case uncons $ stack state of
  Just op:ops ->
    case (runState . runMaybeT) $ advance cfg state of
      Just s' -> advanceLoop cfg s'
      Nothing -> Left $ ExecError { offendingOp = op, stackTrace = state }
  Nothing -> Right state

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

eval :: EvalConfig -> Expr -> Either ExecError Expr
eval cfg e =
  advanceToEnd cfg s0
  where s0 = mkState e
