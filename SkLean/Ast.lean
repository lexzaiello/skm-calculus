import Mathlib.Data.Nat.Notation

structure BindId where
  toNat : ℕ
deriving BEq, Repr

namespace BindId

def succ (id : BindId) : BindId := ⟨id.toNat.succ⟩

instance : LT BindId where
  lt (slf : BindId) (other : BindId) : Prop :=
    slf.toNat < other.toNat

instance : DecidableRel (@LT.lt BindId _) :=
  fun a b => inferInstanceAs (Decidable (a.toNat < b.toNat))

end BindId

inductive SkExpr where
  | k    : SkExpr
  | s    : SkExpr
  | prp  : SkExpr
  | ty   : ℕ      → SkExpr
  | fall : SkExpr → SkExpr → SkExpr
  | call : SkExpr → SkExpr → SkExpr
  | var  : BindId → SkExpr
deriving BEq, Repr

namespace SkExpr

-- TODO: Lemma about index shifting
def with_indices_succ (idx : BindId) (in_expr : SkExpr) : SkExpr :=
  match in_expr with
    | fall bind_ty body =>
      fall (bind_ty.with_indices_succ idx.succ) (body.with_indices_succ idx.succ)
    | var n =>
      if n > idx then
        var n.succ
      else
        var n
    | call lhs rhs =>
      call (lhs.with_indices_succ idx) (rhs.with_indices_succ idx)
    | x => x

def substitute (in_expr : SkExpr) (n : BindId) (with_expr : SkExpr) : SkExpr :=
  let rec substitute' (in_expr : SkExpr) (n : BindId) (with_expr : SkExpr) : SkExpr :=
    match in_expr with
      | fall bind_ty body =>
        fall (substitute' bind_ty n.succ with_expr) (substitute' body n.succ with_expr)
      | var n' => if n == n' then with_expr  else var n'
      | x => x
   substitute' in_expr n (with_indices_succ ⟨1⟩ with_expr)

def body : SkExpr → SkExpr
  | fall _ body => body
  | x => x

def eval_once : SkExpr → Option SkExpr
  | (call (call (call (call k _) _) x) _) => x
  | call (call (call (call (call (call s _) _) _) x) y) z => call (call x z) (call y z)
  | _ => none

end SkExpr
