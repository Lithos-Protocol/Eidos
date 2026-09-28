# Fragment semantics and evidence

## Supported model

| Element | Meaning in Eidos |
| --- | --- |
| `Long` | An integer in the inclusive range −2^63 through 2^63−1, with a range proof |
| `Long.ofInt` | Checked conversion; out-of-range integers produce `arithmeticOverflow` |
| `Long.sub` | Mathematical subtraction followed by checked conversion |
| `Box` | Only the `value` field, in nanoERGs |
| `Context` | `SELF` and the list of outputs |
| `LongExpr.const` | A value already proven to fit in a `Long` |
| `LongExpr.selfValue` | Reads `SELF.value` |
| `LongExpr.outputValue` | Reads an output at a fixed nonnegative index, or fails |
| `LongExpr.sub` | Evaluates operands left to right and performs checked subtraction |
| `BoolExpr.const` | A Boolean constant |
| `BoolExpr.le` | Evaluates operands left to right and compares signed values |
| `BoolExpr.and` | Evaluates the right operand only when the left returns `true` |
| `Accepts` | Boolean evaluation equals `Except.ok true` |

Expressions returning a `Long` and expressions returning a Boolean have
different types. A Boolean cannot accidentally be used as a numeric operand.
All recursive evaluation follows the finite expression tree and terminates.

The index is a Lean `Nat` literal in this fragment; dynamic indices and Ergo's
signed `Int` index semantics are not modeled. Errors preserve failure vs.
successful `false`, but do not reproduce JVM exception classes or messages.

`Box.value` permits every signed `Long`. Valid ledger boxes have additional
restrictions, deliberately not assumed by the general accounting theorem.
The theorem therefore holds over a larger set of contexts, but does not prove
that any chosen context is constructible on the ledger.

## Reference evidence

The implementation was informed by the locally cached published source artifact
[`org.scorexfoundation:sigma-state_2.12:6.0.6` sources](https://repo1.maven.org/maven2/org/scorexfoundation/sigma-state_2.12/6.0.6/sigma-state_2.12-6.0.6-sources.jar),
inspected on 2026-09-28:

- `sigma/ast/trees.scala`: `BinAnd.eval` short-circuits; `ArithOp.Minus` uses
  the numeric implementation selected for its operand type.
- `sigma/data/ExactIntegral.scala`: `LongIsExactIntegral.minus` uses
  `java7.compat.Math.subtractExact`.
- `sigma/ast/transformers.scala`: `ByIndex` without a default performs direct
  collection access, and `ExtractAmount` returns the box's value.
- The [ErgoScript language description](https://docs.ergoplatform.com/dev/scs/sigma/lang-spec/)
  describes signed `Long`, `SELF`, `OUTPUTS`, and nanoERG box values.

The inspected sources JAR has SHA-256
`def07d06ed0f8dff3bfbf41a68d4df1d4a0e448effb46bb95b4d2e9711b45664`.

This is source-informed modeling, not a verified port of that implementation.
Eidos does not claim conformance with all of Sigma 6.0.6, all ErgoTree versions,
or current chain consensus rules. A compiler may lower source constructs into
nodes other than the ones represented here, so source resemblance alone does
not establish a bytecode connection.

## Proof scope and trust

`accepts_iff` proves the exact meaning of successful evaluation for this model
of the reserve rule. `withdrawal_bounded` derives a mathematical value-decrease
bound from it. `checked_withdrawal` adds a nonnegative-reserve hypothesis and
proves that checked subtraction succeeds as well as satisfying the bound.

These are safety implications. They do not imply a feasible transaction,
affordable execution, eventual inclusion, or cryptographic authorization.
The reserve condition does not preserve ownership of that reserve. Reusing the
same output to satisfy multiple inputs is also outside the claimed property.

The initial build was checked with Lean 4.34.1. `ProofAudit.lean` reports only
standard Lean foundational axioms (`propext`, `Quot.sound`, and, for the checked
arithmetic lemmas, `Classical.choice`). No project axioms, unfinished proof terms,
or native-evaluation proof shortcuts are used. Concrete checks use `decide`;
`#eval` in the demo is executable illustration and is not proof evidence.

The proof checker still checks the statement we wrote. A correct theorem about
an inaccurate model or incomplete property would not establish contract safety.

## Unimplemented boundaries

- ErgoScript compilation, ErgoTree decoding, serialization, constant
  segregation, and correspondence to a deployed script.
- Registers, tokens, box IDs, proposition bytes, input/data-input membership,
  authenticated state lineage, and transaction-wide conservation rules.
- Sigma propositions and proofs, authenticated dictionaries, and hashing.
- Cost limits, version switches, storage rent, and other ledger validation paths.
- Multi-transaction state invariants and liveness assumptions.

There is no importer yet. Unsupported operations cannot be constructed with
these expression types; this must not be mistaken for validation of arbitrary
ErgoTree input. A future importer should reject unsupported nodes explicitly.

## Validation commands

```powershell
.\scripts\lake.ps1 build
.\scripts\lake.ps1 env lean Demo.lean
.\scripts\lake.ps1 env lean ProofAudit.lean
```

The initial validation passed the complete Lean build and all 22 concrete
checks, including both signed bounds, both overflow directions, missing outputs,
extra outputs, reserve violations, and lazy Boolean error behavior. It also
checked the general safety and counterexample theorems. No reference-interpreter
differential tests or live-chain tests were run.
