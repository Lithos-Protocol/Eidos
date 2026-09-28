# Eidos

A small Lean 4 library for exploring formal verification of ErgoScript contracts.
The first example proves a reserve accounting property from an executable
expression model, and proves that removing the reserve check makes the property
false.

**Status:** checked proofs about a manually encoded fragment. Eidos does not yet
parse ErgoScript, decode ErgoTrees, or verify deployed contracts.

## Run it

The project pins Lean **4.34.1** and uses only its bundled standard library;
Mathlib and other external Lean packages are not required.

On Windows, the wrapper uses a toolchain extracted into
`.tools/lean-4.34.1-windows/` when present, otherwise your installed Lake:

```powershell
.\scripts\lake.ps1 build
.\scripts\lake.ps1 env lean Demo.lean
.\scripts\lake.ps1 env lean ProofAudit.lean
```

With [Lean/Elan installed](https://lean-lang.org/install/), the equivalent commands
on any supported platform are:

```sh
lake build
lake env lean Demo.lean
lake env lean ProofAudit.lean
```

`lake build` checks the library, all example theorems, and 22 concrete checks.
Warnings, including unfinished proofs, are treated as errors. `Demo.lean` prints
sample evaluations. `ProofAudit.lean` reports the axioms used by the main theorems.
The generated `.lake/` and local `.tools/` directories are ignored by Git.
Toolchain binaries are not included in this repository.

## The first contract

The illustrative source in [contracts/reserve.ergo](contracts/reserve.ergo)
uses a compiler-supplied `Long` constant `RESERVE`, measured in nanoERGs:

```scala
sigmaProp(
  OUTPUTS(0).value <= SELF.value &&
  RESERVE <= OUTPUTS(0).value
)
```

The Boolean body is encoded with library expressions in
[Eidos/Examples/Reserve.lean](Eidos/Examples/Reserve.lean):

```lean
def script (reserve : Long) : BoolExpr :=
  .and (.le (.outputValue 0) .selfValue)
       (.le (.const reserve) (.outputValue 0))
```

Evaluating an expression returns `Except EvalError Bool`: successful `true`,
successful `false`, or an error. `Accepts` means specifically that evaluation
returns successful `true`. Missing outputs and arithmetic overflow are errors.

The property is stated independently of the evaluator:

```text
OUTPUTS(0) exists, and
0 <= SELF.value - OUTPUTS(0).value <= SELF.value - reserve
```

The actual Lean proof is:

```lean
theorem withdrawal_bounded (reserve : Long) (ctx : Context)
    (accepted : Accepts (script reserve) ctx) : WithdrawalBounded reserve ctx := by
  obtain ⟨out, hout, hself, hreserve⟩ := (accepts_iff reserve ctx).1 accepted
  exact ⟨out, hout, by omega, by omega⟩
```

`accepts_iff` connects the executable interpreter to the conditions enforced by
the script, including output existence. `omega` builds arithmetic proofs that
Lean checks. The theorem covers **every** representable reserve and context,
including arbitrary additional outputs, rather than just the sample values.

The specification subtracts mathematical signed integers. A second theorem,
`checked_withdrawal`, connects that result to checked `Long` subtraction: with
a nonnegative reserve, the accepted decrease fits in a `Long` and obeys the same
bound. Arithmetic in the expression evaluator itself never silently wraps.

## The counterexample

With 100 ERG in `SELF` and a reserve of 30 ERG, output zero must retain at least
30 ERG. The decrease can be at most 70 ERG.

| Model scenario | Repaired rule | Vulnerable rule |
| --- | --- | --- |
| Output zero holds 30 ERG | Accepts | Accepts |
| Output zero holds 20 ERG | Rejects | Accepts |
| Output zero is missing | Evaluation error | Evaluation error |

The vulnerable rule omits the reserve check. `vulnerable_counterexample` proves
that the 100→20 ERG context both passes that rule and violates the bound.
`vulnerable_rule_is_not_safe` proves the negation of its universal safety claim.
The counterexample is part of a successful build; no intentionally broken Lean
file needs to be excluded from checking.

## What the library contains

| File | Role |
| --- | --- |
| `Eidos/Ergo/Long.lean` | Signed 64-bit values, checked subtraction, arithmetic lemmas |
| `Eidos/Ergo/Context.lean` | Box-value/context projections and checked output lookup |
| `Eidos/Ergo/Expr.lean` | Small expression language, interpreter, acceptance definition |
| `Eidos/Examples/Reserve.lean` | Contract model, safety proofs, counterexample |
| `EidosTests.lean` | Boundary, failure, short-circuit, and accounting checks |
| `Demo.lean` | Executable walkthrough |
| `ProofAudit.lean` | Theorem dependency inspection |

Use `import Eidos` to access the library. The expression types only expose the
supported operations; there is no fallback that treats unknown Ergo operations
as successful.

## What this establishes

This proves an accounting fact about the library's model. The illustrative
`.ergo` files have **not** been compiled or compared against the reference
interpreter. The manually encoded expressions are not certified translations
of deployed ErgoTree bytes.

Output zero is a designated output, not an authenticated successor. Its value
may satisfy the rule even if its script gives control to someone else. This
example does not establish ownership, script continuity, transaction-wide
accounting, or preservation across transaction sequences. The counterexample is
a model context, not a constructed ledger-valid transaction.

The context omits other box fields and ledger constraints; there is no Sigma
proof verification, cost accounting, storage-rent path, or serialization model.
See [docs/SEMANTICS.md](docs/SEMANTICS.md) for the precise scope and reference
source used when designing the fragment.

The next useful milestone is to compile this same contract with a pinned Sigma
interpreter, import its supported ErgoTree nodes, and compare its reductions
with the Lean evaluator. Those comparisons would provide test evidence for the
bridge; a theorem connecting the representations remains a separate obligation.

## License

Eidos is released under [CC0 1.0 Universal](LICENSE), following the convention
used by Lithos-Client.
