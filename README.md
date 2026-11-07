# Flex

A Lean 4 library for solving Constrained Horn Clauses (CHCs).

## Using as a Dependency

Use Lean **v4.34.0** via `elan`. Add to your `lakefile.toml`:

```toml
[[require]]
name = "Flex"
git = "https://github.com/LeanHorn/Flex"
rev = "main"
```

Fetch and build:

```bash
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build
```

Flex depends on `aesop`, `lean-auto`, `lean-smt`, and `SMTLib-to-Lean`.
The update command skips automatic Mathlib cache downloads. lean-smt downloads
cvc5 automatically; `flex_auto` requires `z3` on `PATH`. For Linux native
dependencies and linker setup, see the [CI workflow](.github/workflows/lean_action_ci.yml).

## Usage

`zap` eliminates acyclic predicates. `fix` synthesizes invariants by predicate
abstraction and leaves any unproved residual obligations as Lean goals.

```lean4
import Flex

example : ∃ k : Int → Prop,
    k 5
    ∧ (∀ i, k i → 1 ≤ i → k (i - 1))
    ∧ (∀ i, k i → 0 ≤ i) := by
  fix
```

By default, `fix` starts with a [qualifier bank](Flex/PA/Qualifier.lean) for
`Int`, `Nat`, and `Bool`, together with definitions tagged `@[qualif]`.
If synthesis fails, it grows the bank through Basic, Standard, then Deep scraping.

## Scraping and SMT Oracles

Scraping adds qualifier candidates from the goal and definitions:

| Option | Candidates collected |
| --- | --- |
| `fix (scrape := auto)` | Incremental escalation; the default. |
| `fix (scrape := no)` | Bank and tagged qualifiers only. |
| `fix (scrape := basic)` | Clause conclusions and explicitly selected definitions. |
| `fix (scrape := standard)` | Also premises, bounded guarded arithmetic qualifiers, Boolean observations, and relevant definitions. |
| `fix (scrape := deep)` | Also explores helper definitions and generalizes numeric templates, within search limits. |

Explicit levels run once. All synthesis stages share a 60-second budget,
set by `flex.fixpointTimeout`; certification follows a successful search.
Add `(defs := [fib])` to select definitions explicitly.
Use `set_option flex.reportQualifiers true` to inspect scraped candidates in the Infoview.
Disable guarded templates with `(scrapeConfig := { maxGuardedQualifiers := 0 })`.
By default, `fix` batches SMT checks in short-lived Z3 processes,
rechecks affected clauses after weakening, and uses kernel-checked SMT proofs and
Lean automation for certification and residual goals. `flex_discharge` runs this
proof automation separately, leaving unsolved goals for manual proof.

Synthesis checks use one exact SMT encoding (`Flex/SMT/Encode.lean`): `Int`, `Nat`
(nonnegative `Int`), `Bool`/`Prop`, functions as arrays, and records, `Option`, `List` and
other non-indexed inductives as monomorphized datatypes, and nonempty opaque types as
uninterpreted sorts. Definitions become `define-fun`, or
uninterpreted functions when recursive. A satisfiable query counts as a counterexample only
when nothing was left uninterpreted; queries the encoding cannot decide fall back to Lean
automation.

| Option | Default | Effect |
| --- | --- | --- |
| `flex.smt.uninterpretedDefs` | `false` | Leave every definition uninterpreted. |
| `flex.smt.encodeNonlinear` | `false` | Encode products of non-literals and division or modulo by a non-literal. |
| `flex.smt.encodeQuantifiers` | `false` | Encode lambdas and the quantifiers the solver cannot skolemize (see below). |

Queries are first flattened into clauses; clause variables are SMT constants, not quantifiers.
As in Liquid Fixpoint, existentials in premises are passed to the solver, which skolemizes them,
and so are universals in a clause's head. Quantifiers at the other polarity, under other
operators, or in definition bodies need `flex.smt.encodeQuantifiers`. When a construct
is not encoded, a query that uses it is not sent to the solver, and a definition whose body
uses it is left uninterpreted.

Optional SMT backends can be selected separately for synthesis and proofs:

```lean4
fix (synth := flex_auto [*]) (proof := flex_smt [*])
```

These options try the selected backend before Lean automation. `flex_auto` uses
a trusted SMT axiom; `flex_smt` reconstructs Lean proofs. Synthesis proof terms
are discarded; only proof-phase evidence enters the final certificate.

See [Demo/Basic.lean](Demo/Basic.lean) for elimination examples and
[Demo/Fix.lean](Demo/Fix.lean) for invariants, scraping, and SMT oracles.

## CHC Solvers

Import `Flex.Tactic.Tactics.Spacer` or `Flex.Tactic.Tactics.Eldarica` for the
`spacer` and `eldarica` tactics. They report and instantiate solver invariants,
certify predicate heads with `grind`, and leave one structured VC for subsequent tactics.
Install `z3` and `eld` on `PATH`, or set `flex.spacer.executable` and
`flex.eldarica.executable`. See [Demo/Spacer.lean](Demo/Spacer.lean) for both.

`Flex.CHC.solveGoal` provides the underlying library API, including complete
certification, residual obligations, and rollback on failure.
Export supports Int/Bool constraints and rejects unsupported theories without
abstraction.

## `flex`

`import Flex` provides `flex`: preprocessing, optional nesting, Zap, then Fix
(with incremental scraping) and Spacer/Eldarica. It uses checked SMT and Lean automation
for proofs, retaining validated invariants and a structured residual VC when
manual work remains. Failed phases preserve earlier progress.

```lean4
flex
flex (backends := [fix]) (scrape := basic)
flex (backends := []) (config := { nesting := true }) -- Zap only
flex (config := { postprocess := true }) -- optional witness simplification
flex (config := { totalTimeout := 60 }) -- shared pipeline budget; also the default
```

Only True/False preprocessing is enabled by default. Nesting, postprocessing, and
separating κ-free clauses (`splitFree := true`) are opt-in. Postprocessing runs once
after Zap makes progress and skips expensive or growing witness rewrites.
Use `preprocess := false` to disable preprocessing.

Use `proof := ...` for certification and `closer := ...` for residual proofs.
The whole tactic shares a 30-second budget, including cleanup. Expiry requests
cancellation and preserves the latest checkpoint; calls that do not respond to
cancellation can overrun. `trace.flex.timing` shows phase times, `report := true`
enables progress messages, and `trace.flex` exposes failed attempts. Unvalidated solver
candidates require the explicit `keepCandidates := true` exploratory option;
refuted candidates are discarded and every unproved obligation remains a goal.
See [Demo/Flex.lean](Demo/Flex.lean) for complete and partial proofs.
