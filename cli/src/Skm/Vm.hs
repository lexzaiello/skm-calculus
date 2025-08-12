module Skm.Vm where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Control.Monad.Trans.Except
import Control.Monad.State.Lazy
import Skm.Ast (SkExpr(..))
import Skm.Compiler.Ast (OptionalTy(..))
import Skm.Eval (ReductionMode(..), EvalConfig, EvalConfig(..))

-- One-step evaluation valid reductions
-- Not defined for left-side evaluation
data Step = KCall
  | SCall
  | MCall
  | ICall
  | BCall
  | B0Call
  | CCall
  | S'Call
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
  , err         :: ExecError
  }
  | EmptyStack
  | NoResult
  | NoType
    { offendingExpression :: SkExpr
    }
  | IncorrectType
    { offendingE          :: SkExpr
    , expectedType        :: SkExpr
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

pop :: ExceptT ExecError (State ExecState) Op
pop = (ExceptT . state) $ \st ->
  case stack st of
    (x:xs) -> (pure x, st { stack = xs, trace = x:trace st })
    []     -> (Left EmptyStack, st)

popE :: ExceptT ExecError (State ExecState) SkExpr
popE = (ExceptT . state) $ \st ->
  case register st of
    (x:xs) -> (pure x, st { register = xs })
    []     -> (Left EmptyStack, st)

pushMany :: [Op] -> State ExecState ()
pushMany = mapM_ push

mkState :: SkExpr -> ExecState
mkState e = snd $ runState (do
    pushMany [TryStep, Rfl e]
  ) $ ExecState { trace = [], stack = [], register = [], cache = HM.fromList [] }

check :: EvalConfig -> SkExpr -> OptionalTy SkExpr -> ExceptT ExecError (State ExecState) ()
check cfg e t = do
  let s0 = mkState (Call M e)
  let (err, s) = runState (runExceptT $ advanceToEnd cfg) s0

  _ <- (ExceptT . pure) err

  case outE s of
    Left _ ->
      (ExceptT . pure . Left) $ NoType { offendingExpression = e }
    Right t0' ->
      case t of
        (OptionalTy (Just t)) ->
          if t0' == t then
            pure ()
          else
            (ExceptT . pure . Left) $ IncorrectType { offendingE = e, expectedType = t }
        (OptionalTy Nothing) -> pure ()

advance :: EvalConfig -> ExceptT ExecError (State ExecState) ()
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

      (lift . pushMany) [Rfl (Call lhs rhs)]
    Rfl e -> (lift . pushE) e
    EvalOnce ICall -> do
      x <- popE

      (lift . pushMany) [TryStep, Rfl x]
    EvalOnce BCall -> do
      f <- popE
      g <- popE
      x <- popE

      (lift . pushMany) [TryStep, Rfl (Call f (Call g x))]
    EvalOnce B0Call -> do
      p <- popE

      (lift . pushMany) [TryStep, Rfl p]
    EvalOnce CCall -> do
      f <- popE
      g <- popE
      x <- popE

      (lift . pushMany) [TryStep, Rfl (Call (Call f x) g)]
    EvalOnce S'Call -> do
      c <-popE
      f <- popE
      g <- popE
      x <- popE

      (lift . pushMany) [TryStep, Rfl (Call (Call c (Call f x)) (Call g x))]
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

      (lift . pushMany) [TryStep, Rfl (Call (Call M lhs) rhs)]
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
            (Call M (Call M M)) -> pure [Rfl e]
            -- S' c f g x -> c (f x) (g x)
            (Call (Call (Call S (Call (Call S (Call K c)) f)) g) x) -> pure [EvalOnce S'Call, Rfl c, Rfl f, Rfl g, Rfl x]
            -- C f g x -> f x g
            (Call (Call (Call S f) (Call K g)) x) -> pure [EvalOnce CCall, Rfl f, Rfl g, Rfl x]
            -- B p i -> p
            (Call (Call S (Call K f)) _g) -> pure [EvalOnce B0Call, Rfl f]
             -- B f g x
            (Call (Call (Call S (Call K f)) g) x) -> pure [EvalOnce BCall, Rfl f, Rfl g, Rfl x]
            (Call (Call (Call S K) K) x) -> pure [EvalOnce ICall, Rfl x]
            (Call (Call K x) y) -> pure [EvalOnce KCall, Rfl x]
            (Call (Call (Call S x) y) z) -> pure [EvalOnce SCall, Rfl x, Rfl y, Rfl z]
            (Call M K) -> pure [EvalOnce Mk]
            (Call M S) -> pure [EvalOnce Ms]
            (Call M (Call lhs rhs)) -> pure [EvalOnce MCall, Rfl lhs, Rfl rhs]
            (Call lhs rhs) -> (do
              lhs' <- (lift . tryMemo) lhs

              case lhs' of
                Just l ->
                  pure [TryStep, Memoize, Rfl e, Dup, Lhs, Rfl l, Rfl rhs]
                Nothing ->
                  pure [TryStep, Memoize, Rfl e, Dup, Lhs, TryStep, Rfl lhs, Rfl rhs])
            x -> pure [Rfl x])

          (lift . pushMany) ([Memoize, Rfl e, Dup] ++ ops)

-- There should be only a single expression in the register at the end of execution
outE :: ExecState -> Either ExecError SkExpr
outE s = case register s of
  [e]  -> pure e
  _    -> Left NoResult

lastE :: ExecState -> Either ExecError SkExpr
lastE s = case register s of
  e:_ -> pure e
  _   -> Left NoResult

reduceAll :: EvalConfig -> ExceptT ExecError (State ExecState) ExecState
reduceAll cfg = do
  e <- popE
  case e of
    c@(Call lhs rhs) -> do
      _ <- (if mode cfg == Strict then
        (lift . pushMany) [TryStep, Lhs, TryStep, Rfl lhs, TryStep, Rfl rhs]
      else
        (lift . pushMany) [TryStep, Lhs, TryStep, Rfl lhs, Rfl rhs])
      _ <- advanceToEnd cfg
      get
    _ -> get

advanceN :: EvalConfig -> Int -> ExceptT ExecError (State ExecState) ()
advanceN cfg n
  | n <= 0 = pure ()
  | otherwise = advance cfg >> advanceN cfg (n - 1)

advanceToEnd :: EvalConfig -> ExceptT ExecError (State ExecState) ExecState
advanceToEnd cfg = do
  stk <- lift $ gets stack
  case stk of
    [] -> lift get
    op:_ -> do
      res <- withExceptT (\e -> ExecError { offendingOp = Just op, stackTrace = undefined, err = e }) $
               advance cfg
      advanceToEnd cfg

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

eval :: EvalConfig -> SkExpr -> Either ExecError SkExpr
eval cfg e     = do
  let (e, sFinal) = (if mode cfg == Strict then
                       runState (runExceptT $ advanceToEnd cfg >> reduceAll cfg) s0
                     else
                       runState (runExceptT $ advanceToEnd cfg) s0)
  _ <- e
  eFinal <- outE sFinal
  pure eFinal
  where s0 = mkState e

evalN :: EvalConfig -> Int -> SkExpr -> Either ExecError SkExpr
evalN cfg n e = do
  let (e, sFinal) = runState (runExceptT $ advanceN cfg n) s0
  e
  outE sFinal
  where s0 = mkState e
