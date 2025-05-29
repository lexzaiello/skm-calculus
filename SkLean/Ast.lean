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
def with_indices_plus (in_expr : SkExpr) (shift_by : BindId) : SkExpr :=
  match in_expr with
    | fall bind_ty body =>
      fall (bind_ty.with_indices_plus shift_by.succ) (body.with_indices_plus shift_by.succ)
    | var n =>
      if n > shift_by then
        var ⟨n.toNat + shift_by.toNat⟩
      else
        var n
    | call lhs rhs =>
      call (lhs.with_indices_plus shift_by) (rhs.with_indices_plus shift_by)
    | x => x

def substitute (in_expr : SkExpr) (n : BindId) (with_expr : SkExpr) : SkExpr :=
  match in_expr with
    | fall bind_ty body =>
      fall (bind_ty.substitute n.succ with_expr) (body.substitute n.succ with_expr)
    | var n' => if n == n' then with_expr.with_indices_plus n else var n'
    | x => x

example : (fall (ty 0) (var ⟨2⟩)).with_indices_plus ⟨1⟩ = (fall (ty 0) (var ⟨2⟩)) := by
  repeat unfold with_indices_plus
  simp
  intro h
  unfold BindId.succ
  simp
  contradiction

example : (fall (ty 0) (var ⟨1⟩)).substitute ⟨0⟩ (var ⟨2⟩) = (fall (ty 0) (var ⟨3⟩)) := by
  unfold substitute
  simp
  repeat unfold substitute
  simp
  split
  repeat unfold with_indices_plus
  simp
  split
  simp
  unfold BindId.succ
  simp
  contradiction
  simp_all
  repeat unfold BindId.succ at *
  simp_all
  contradiction

example : (fall (ty 0) (var ⟨1⟩)).substitute ⟨0⟩ (fall (ty 0) (var ⟨4⟩)) = (fall (ty 0) ((fall (ty 0) (var ⟨6⟩)))) := by
  unfold substitute
  simp
  repeat unfold substitute
  simp
  split
  case isTrue h =>
    repeat unfold with_indices_plus
    simp
    repeat unfold BindId.succ at *
    simp_all
    unfold LT.lt
    unfold BindId.instLT
    simp
  case isFalse h =>
    simp_all
    contradiction

def body : SkExpr → SkExpr
  | fall _ body => body
  | x => x

def eval_once : SkExpr → SkExpr
  | (call (call (call (call k _) _) x) _) => x
  | call (call (call (call (call (call s _) _) _) x) y) z => call (call x z) (call y z)
  | x => x

end SkExpr
