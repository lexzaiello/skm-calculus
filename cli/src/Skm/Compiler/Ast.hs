module Skm.Compiler.Ast where

import Data.List (intercalate)
import Text.Read (readMaybe)

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

changeVariables :: String -> Int -> ReadableExpr -> ReadableExpr
changeVariables fromV toV (HFall binder maybeTy body) = HFall binder (doChange <$> maybeTy) (doChange body)
  where doChange = changeVariables fromV (toV + 1)
changeVariables fromV toV (HLam binder maybeTy body)  = HLam binder  (doChange <$> maybeTy) (doChange body)
  where doChange = changeVariables fromV (toV + 1)
changeVariable fromV toV  (HVar v)
  | v == fromV = HVar $ show toV
  | otherwise  = HVar v
changeVariable _ _ e = e

parseReadableExpr :: ReadableExpr -> Maybe Expr
parseReadableExpr Hs                         = pure S
parseReadableExpr Hk                         = pure K
parseReadableExpr Hm                         = pure M
parseReadableExpr (HVar n)                   = Var <$> readMaybe n
parseReadableExpr (HApp lhs rhs)             = do
  lhs' <- parseReadableExpr lhs
  rhs' <- parseReadableExpr rhs

  pure $ App lhs' rhs'
parseReadableExpr (HLam binder maybeTy body) =
  let ty'  = changeVariables binder 0 <$> maybeTy
      body = changeVariables binder 0 body
  in do
    parsedBody <- parseReadableExpr body
    pure $ Lam (ty' >>= parseReadableExpr) parsedBody
parseReadableExpr (HFall binder maybeTy body) =
  let ty'  = changeVariables binder 0 <$> maybeTy
      body = changeVariables binder 0 body
  in do
    parsedBody <- parseReadableExpr body
    pure $ Fall (ty' >>= parseReadableExpr) parsedBody

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
