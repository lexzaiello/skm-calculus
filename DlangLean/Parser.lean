import Parser
import DlangLean.CoC

open Parser Char

abbrev Ident := String

-- e := Type n | Prop | var | e e | λx:e.e | ∀x:e.e

inductive LToken where
  | lam    : LToken
  | fall   : LToken
  | lparen : LToken
  | rparen : LToken
  | ident  : Ident → LToken
  | num    : ℕ     → LToken
  | ty     : LToken
  | prp    : LToken
  | colon  : LToken

def tokenizel : SimpleParser Substring Char LToken := first sorry

inductive DExpr where
  -- let blah := blah'
  | let_e      : DExpr  → DExpr → DExpr
  | identifier : Ident  → DExpr
  -- Typed lambda expression
  | raw_l_e    : LExpr  → DExpr
  | match_e    : DExpr  → List DExpr → DExpr

inductive DStmt where
  -- def blah : blah := blah
  | definition : String → List (Ident × LExpr) → Expr → Expr → DStmt

