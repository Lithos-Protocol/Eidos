import Eidos

namespace Eidos.Tests
open Ergo Examples.Reserve

def context (selfValue : Long) (outputValues : List Long) : Context :=
  ⟨⟨selfValue⟩, outputValues.map Box.mk⟩

def hundred : Long := ⟨100000000000, by decide⟩
def thirty : Long := ⟨30000000000, by decide⟩
def twenty : Long := ⟨20000000000, by decide⟩

-- Exact reserve, no decrease, and arbitrary additional outputs.
example : Accepts (script thirty) (context hundred [thirty]) := by decide
example : Accepts (script thirty) (context hundred [hundred]) := by decide
example : Accepts (script thirty) (context hundred [thirty, twenty, hundred]) := by decide

-- Below reserve, reserve above input, and a forbidden increase.
example : ¬ Accepts (script thirty) (context hundred [twenty]) := by decide
example : ¬ Accepts (script hundred) (context thirty [thirty]) := by decide
example : ¬ Accepts (script thirty) (context thirty [hundred]) := by decide

-- Absence is an evaluation error, distinct from a Boolean rejection.
example : (script thirty).eval (context hundred []) =
    .error (.outputOutOfBounds 0) := by decide
example : ¬ Accepts (script thirty) (context hundred []) := by decide
example : (LongExpr.outputValue 3).eval (context hundred [thirty]) =
    .error (.outputOutOfBounds 3) := by decide

-- The full signed range is representable; conversions outside it fail.
example : (Long.ofInt Long.minValue).map Subtype.val = .ok Long.minValue := by decide
example : (Long.ofInt Long.maxValue).map Subtype.val = .ok Long.maxValue := by decide
example : Long.ofInt (Long.maxValue + 1) = .error .arithmeticOverflow := by decide
example : Long.ofInt (Long.minValue - 1) = .error .arithmeticOverflow := by decide

def maxLong : Long := ⟨9223372036854775807, by decide⟩
def minLong : Long := ⟨-9223372036854775808, by decide⟩
def one : Long := ⟨1, by decide⟩
def negativeOne : Long := ⟨-1, by decide⟩

-- Both overflow directions; ordinary negative subtraction remains signed.
example : Long.sub maxLong negativeOne = .error .arithmeticOverflow := by decide
example : Long.sub minLong one = .error .arithmeticOverflow := by decide
example : (Long.sub twenty thirty).map Subtype.val = .ok (-10000000000) := by decide
example : (Long.sub hundred thirty).map Subtype.val = .ok 70000000000 := by decide
example : Accepts (script maxLong) (context maxLong [maxLong]) := by decide

-- Boolean evaluation follows BinAnd, including its error behavior.
def failingComparison : BoolExpr := .le (.outputValue 0) .selfValue
example : (BoolExpr.and (.const false) failingComparison).eval (context hundred []) =
    .ok false := by decide
example : (BoolExpr.and (.const true) failingComparison).eval (context hundred []) =
    .error (.outputOutOfBounds 0) := by decide
example : (BoolExpr.and failingComparison (.const false)).eval (context hundred []) =
    .error (.outputOutOfBounds 0) := by decide
example : (LongExpr.sub (.const maxLong) (.const negativeOne)).eval
    (context hundred []) = .error .arithmeticOverflow := by decide

-- Removing the reserve check makes the universal security property false.
theorem vulnerable_rule_is_not_safe :
    ¬ (∀ ctx, Accepts vulnerableScript ctx → WithdrawalBounded exampleReserve ctx) := by
  intro h
  exact vulnerable_counterexample.2 (h attackContext vulnerable_counterexample.1)

end Eidos.Tests
