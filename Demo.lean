import EidosTests

open Eidos.Ergo Eidos.Examples.Reserve Eidos.Tests

-- Run with: lake env lean Demo.lean
#eval ("100 -> 30 ERG, reserve 30", (script thirty).eval (context hundred [thirty]))
#eval ("100 -> 20 ERG, reserve 30", (script thirty).eval attackContext)
#eval ("same context, vulnerable rule", vulnerableScript.eval attackContext)
#eval ("missing output zero", (script thirty).eval (context hundred []))
#eval ("Long.max - (-1)", (Long.sub maxLong negativeOne).map Subtype.val)

-- These are universally quantified theorems, not results of the examples above.
#check withdrawal_bounded
#check checked_withdrawal
#check vulnerable_rule_is_not_safe
