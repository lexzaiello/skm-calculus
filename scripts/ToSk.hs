data LExpr = Lam LExpr
  | Var Int
  | App LExpr LExpr
  | Me
  | Ke
  | Se

data SkExpr = S
  | K
  | M
  | Call SkExpr SkExpr
  | Const String
  | Placeholder

tosk :: LExpr -> SkExpr
tosk Me = M
tosk Se = S
tosk Ke = K
tosk (Lam x (Var 1)) = Call (Call (S (M K)) K) K
tosk (Lam x (App lhs rhs)) = let sklhs = (tosk $ Lam x lhs) in
  let skrhs = (tosk $ Lam x rhs) in
  (Call (Call S sklhs) skrhs)
tosk (Lam x otherwise) = Call K (tosk otherwise)
tosk (App lhs rhs) = Call (tosk lhs) (tosk rhs)
tosk (Var bruh) = Call K (Const bruh)

typeof :: SkExpr -> SkExpr
typeof x = (Call M x)

typify :: SkExpr -> SkExpr
typify (Call K a) = (Call (Call (Call K (Call M a)) Placeholder) a)
typify ((Call K a) b) = (Call (Call (Call (Call K (Call M a)) (Call M b)) a) b)
typify (Call (Call (Call S x) y) z) = (((Call S (Call M x)) (Call M y)) (Call M z))

eval :: SkExpr -> SkExpr
eval (Call (Call (Call (Call K a) b) x) y) = x
eval (Call (Call (Call (Call (Call (Call S a) b) c) x) y) z) = eval (Call (Call x z) (Call y z))
eval x = x

instance Show SkExpr where
  show M = "M"
  show S = "S"
  show K = "K"
  show (Call lhs rhs) = "(" ++ (show lhs) ++ " " ++ (show rhs) ++ ")"
  show (Const c) = show c

main :: IO ()
main =
  putStrLn $ show $ eval $ tosk (Lam (Lam (App (App (App Ke (App Me (Var 1))) (Var 2)) (Var 1))))
