module Skm.Compiler.Ast where

import Data.List (intercalate)

-- Calculus of constructions expr, using 0-indexed De Bruijn Indices
-- Lambda abstractions are optionally typed. Types are inferred
-- where possible.
data Expr = Lam (Maybe Expr) Expr
  | Fall (Maybe Expr) Expr
  | Var Int
  | App Expr Expr
  | S
  | K
  | M
  deriving (Eq, Ord)

-- Human readable, not used anywhere except for serialization purposes

data ReadableExpr = HLam String (Maybe ReadableExpr) ReadableExpr
  | HFall String (Maybe ReadableExpr) ReadableExpr
  | HVar String
  | HApp ReadableExpr ReadableExpr
  | Hs
  | Hk
  | Hm
  deriving (Eq, Ord)

unwordtokens :: [[Token]] -> [Token]
unwordtokens = intercalate [Space]

tokenize :: ReadableExpr -> [[Token]]
tokenize Hs = [pure Ts]
tokenize Hk = [pure Tk]
tokenize Hm = [pure Tm]
tokenize (HLam  binder (Just bind_ty) body) = [[Lambda], [LParen, Ident binder], [Colon], ((unwordtokens $ tokenize bind_ty) ++ [RParen]), [FatArrow], (unwordtokens $ tokenize body)]
tokenize (HLam  binder Nothing        body) = [[Lambda], [Ident binder], [FatArrow], (unwordtokens $ tokenize body)]
tokenize (HFall binder (Just bind_ty) body) = [[TFall], [LParen, (Ident binder)], [Colon], ((unwordtokens $ tokenize bind_ty) ++ [RParen, Comma]), (unwordtokens $ tokenize body)]
tokenize (HFall binder Nothing        body) = [[TFall], [(Ident binder), Comma], (unwordtokens $ tokenize body)]
tokenize (HVar v)       = [pure (Ident v)]
tokenize (HApp lhs rhs) = [[LParen] ++ (unwordtokens $ tokenize lhs), (unwordtokens $ tokenize rhs) ++ [RParen]]

data Token = LParen
  | RParen
  | Lambda
  | Space
  | FatArrow
  | TFall
  | Comma
  | Def
  | Colon
  | Eq
  | Ident String
  | Ts
  | Tk
  | Tm
  deriving (Eq, Ord)

instance Show Token where
  show LParen     = "("
  show RParen     = ")"
  show Space      = " "
  show FatArrow   = "=>"
  show Def        = "def"
  show Colon      = ":"
  show Eq         = "="
  show (Ident i)  = i
  show Lambda     = "λ"
  show Ts         = "S"
  show Tk         = "K"
  show Tm         = "M"
  show TFall      = "∀"
  show Comma      = ","
