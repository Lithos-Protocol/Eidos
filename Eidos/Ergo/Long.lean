import Std

namespace Eidos.Ergo

deriving instance DecidableEq for Except

inductive EvalError where
  | arithmeticOverflow
  | outputOutOfBounds (index : Nat)
  deriving Repr, DecidableEq

/-- Signed 64-bit values. The bounds are part of the type, not assumed by proofs. -/
abbrev Long := { n : Int // -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 }

namespace Long

def minValue : Int := -9223372036854775808
def maxValue : Int := 9223372036854775807

/-- Checked conversion: out-of-range values fail instead of wrapping. -/
def ofInt (n : Int) : Except EvalError Long :=
  if h : minValue ≤ n ∧ n ≤ maxValue then .ok ⟨n, h⟩
  else .error .arithmeticOverflow

def sub (x y : Long) : Except EvalError Long := ofInt (x.val - y.val)

@[simp] theorem ofInt_eq_ok_iff (n : Int) (x : Long) :
    ofInt n = .ok x ↔ n = x.val := by
  unfold ofInt
  split
  · simp only [Except.ok.injEq, Subtype.ext_iff]
  · rename_i h
    constructor
    · intro impossible
      cases impossible
    · intro hn
      exact False.elim (h (hn ▸ x.property))

@[simp] theorem sub_eq_ok_iff (x y z : Long) :
    sub x y = .ok z ↔ x.val - y.val = z.val := by
  exact ofInt_eq_ok_iff _ _

/-- A decrease between nonnegative Long values can be computed without overflow. -/
theorem sub_nonnegative (x y : Long) (hy : 0 ≤ y.val) (hxy : y.val ≤ x.val) :
    ∃ z, sub x y = .ok z ∧ z.val = x.val - y.val ∧ 0 ≤ z.val := by
  have hx := x.property
  have hr : -9223372036854775808 ≤ x.val - y.val ∧
      x.val - y.val ≤ 9223372036854775807 := by omega
  exact ⟨⟨x.val - y.val, hr⟩, (sub_eq_ok_iff _ _ _).2 rfl, rfl,
    show 0 ≤ x.val - y.val from by omega⟩

end Long
end Eidos.Ergo
