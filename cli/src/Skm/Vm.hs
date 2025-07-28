module Skm.Vm where

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
  | Trans
  -- For normal forms
  | Rfl Expr
  | EvalOnce Step

type Trace    = [Op]
type Stack    = [Op]
type Register = [Expr]

type ExecState = (Stack, Trace)

push :: Op -> State ExecState ()
push = modify . add
  where add op (s, t) = (op:s, t:s)

pop :: State ExecState (Maybe Op)
pop = do
  op <- gets (fst <$> uncons)
  modify sub
  pure op
  where sub (o:s, t) = (s, t)

advance :: State ExecState ()
advance = runMaybeT doAdvance
  where doAdvance :: MaybeT (State ExecState) ()
        doAdvance = do
          o <- pop

          case o of
            Lhs -> do
              lhs <- popRfl
              rhs <- popRfl


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

eval :: EvalConfig -> Expr -> Expr

