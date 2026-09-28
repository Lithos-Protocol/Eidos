import Eidos.Ergo.Long

namespace Eidos.Ergo

/-- Only the box field used by this fragment; this is not a ledger-validity model. -/
structure Box where
  value : Long
  deriving Repr, DecidableEq

/-- A projection of the script context, with arbitrary extra outputs allowed. -/
structure Context where
  self : Box
  outputs : List Box
  deriving Repr, DecidableEq

def Context.outputValue (ctx : Context) (index : Nat) : Except EvalError Long :=
  match ctx.outputs[index]? with
  | some box => .ok box.value
  | none => .error (.outputOutOfBounds index)

end Eidos.Ergo
