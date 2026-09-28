import Eidos.Ergo.Context

namespace Eidos.Ergo

/-- A deliberately small, typed-by-construction expression fragment. -/
inductive LongExpr where
  | const (value : Long)
  | selfValue
  | outputValue (index : Nat)
  | sub (left right : LongExpr)
  deriving Repr

inductive BoolExpr where
  | const (value : Bool)
  | le (left right : LongExpr)
  | and (left right : BoolExpr)
  deriving Repr

def LongExpr.eval (ctx : Context) : LongExpr → Except EvalError Long
  | .const value => .ok value
  | .selfValue => .ok ctx.self.value
  | .outputValue index => ctx.outputValue index
  | .sub left right => do
      let x ← left.eval ctx
      let y ← right.eval ctx
      Long.sub x y

def BoolExpr.eval (ctx : Context) : BoolExpr → Except EvalError Bool
  | .const value => .ok value
  | .le left right => do
      let x ← left.eval ctx
      let y ← right.eval ctx
      pure (decide (x.val ≤ y.val))
  | .and left right => do
      let b ← left.eval ctx
      if b then right.eval ctx else pure false

/-- Successful Boolean reduction only; Sigma proofs and ledger validation are out of scope. -/
def Accepts (script : BoolExpr) (ctx : Context) : Prop :=
  script.eval ctx = .ok true

instance (script : BoolExpr) (ctx : Context) : Decidable (Accepts script ctx) :=
  inferInstanceAs (Decidable (script.eval ctx = .ok true))

theorem error_not_accepted (script : BoolExpr) (ctx : Context) (err : EvalError)
    (h : script.eval ctx = .error err) : ¬ Accepts script ctx := by
  simp [Accepts, h]

end Eidos.Ergo
