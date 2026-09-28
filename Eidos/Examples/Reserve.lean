import Eidos.Ergo.Expr

namespace Eidos.Examples.Reserve
open Ergo

/-- Model of the Boolean body in `contracts/reserve.ergo`. -/
def script (reserve : Long) : BoolExpr :=
  .and (.le (.outputValue 0) .selfValue)
       (.le (.const reserve) (.outputValue 0))

/-- Deliberately missing the reserve check. -/
def vulnerableScript : BoolExpr := .le (.outputValue 0) .selfValue

/-- The accounting property is stated separately from the evaluator. -/
def WithdrawalBounded (reserve : Long) (ctx : Context) : Prop :=
  ∃ out, ctx.outputs[0]? = some out ∧
    0 ≤ ctx.self.value.val - out.value.val ∧
    ctx.self.value.val - out.value.val ≤ ctx.self.value.val - reserve.val

/-- Exact characterization, including the requirement that OUTPUTS(0) exists. -/
theorem accepts_iff (reserve : Long) (ctx : Context) :
    Accepts (script reserve) ctx ↔
      ∃ out, ctx.outputs[0]? = some out ∧
        out.value.val ≤ ctx.self.value.val ∧ reserve.val ≤ out.value.val := by
  cases h : ctx.outputs with
  | nil => simp [Accepts, script, BoolExpr.eval, LongExpr.eval, Context.outputValue,
      bind, Except.bind, h]
  | cons out rest =>
      by_cases hle : out.value.val ≤ ctx.self.value.val
      · simp [Accepts, script, BoolExpr.eval, LongExpr.eval, Context.outputValue,
          bind, pure, Except.bind, Except.pure, h, hle]
      · simp [Accepts, script, BoolExpr.eval, LongExpr.eval, Context.outputValue,
          bind, pure, Except.bind, Except.pure, h, hle]

/-- Every accepted context obeys the withdrawal bound, for every representable reserve. -/
theorem withdrawal_bounded (reserve : Long) (ctx : Context)
    (accepted : Accepts (script reserve) ctx) : WithdrawalBounded reserve ctx := by
  obtain ⟨out, hout, hself, hreserve⟩ := (accepts_iff reserve ctx).1 accepted
  exact ⟨out, hout, by omega, by omega⟩

/-- For a nonnegative reserve, actual checked Long subtraction also succeeds. -/
theorem checked_withdrawal (reserve : Long) (ctx : Context)
    (nonnegative : 0 ≤ reserve.val) (accepted : Accepts (script reserve) ctx) :
    ∃ out amount, ctx.outputs[0]? = some out ∧
      Long.sub ctx.self.value out.value = .ok amount ∧
      0 ≤ amount.val ∧ amount.val ≤ ctx.self.value.val - reserve.val := by
  obtain ⟨out, hout, hself, hreserve⟩ := (accepts_iff reserve ctx).1 accepted
  obtain ⟨amount, hsub, hvalue, hnonneg⟩ :=
    Long.sub_nonnegative ctx.self.value out.value (by omega) hself
  exact ⟨out, amount, hout, hsub, hnonneg, by omega⟩

/-- 100 ERG in, 20 ERG at output zero; other ledger fields are not modeled. -/
def attackContext : Context :=
  { self := ⟨⟨100000000000, by decide⟩⟩
    outputs := [⟨⟨20000000000, by decide⟩⟩] }

def exampleReserve : Long := ⟨30000000000, by decide⟩

/-- The unsafe rule accepts an 80 ERG decrease despite a 70 ERG bound. -/
theorem vulnerable_counterexample :
    Accepts vulnerableScript attackContext ∧
      ¬ WithdrawalBounded exampleReserve attackContext := by
  constructor
  · decide
  · simp [WithdrawalBounded, attackContext, exampleReserve]

theorem repaired_rejects_counterexample :
    ¬ Accepts (script exampleReserve) attackContext := by decide

end Eidos.Examples.Reserve
