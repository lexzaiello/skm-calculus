import DlangLean.CoC
import Mathlib.Tactic

open LExpr

def implies (a : LExpr) (b : LExpr) : LExpr := fall a b

def and (a : LExpr) (b : LExpr) : LExpr :=
  fall prp $ implies (implies a (implies b (var 1)) sorry sorry) sorry sorry sorry

→



#check bind
