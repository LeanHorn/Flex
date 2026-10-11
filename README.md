# Flex

A Lean 4 library for a constraint-solving framework for Constrained Horn Clauses (CHCs).

---

## Using as a Dependency

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) installed via `elan`

### Step 1 — Add to your `lakefile.toml`

```toml
[[require]]
name = "Flex"
git = "https://github.com/jam-khan/Flex"
rev = "main"
```

### Step 2 — Fetch the dependency

```bash
lake update
```

This clones the repo into `.lake/packages/Flex/` using your local Git credentials.

### Step 3 — Build

```bash
lake build
```

> **Note:** Flex uses Lean `v4.33.1` and pins `aesop`, `lean-auto`, `lean-smt`,
> `cvc5`, and [SMTLib-to-Lean](https://github.com/LeanHorn/SMTLib-to-Lean).
> The shared dependencies use SMTLib-to-Lean's revisions. `flex_auto` needs
> `z3` on `PATH`; lean-smt downloads its cvc5 native library during the first
> build. Mathlib is a transitive dependency.
> `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` skips automatic Mathlib cache downloads; importing
> SMTLib-to-Lean still requires building or fetching its Mathlib dependencies.

---

## Importing

A single import gives you the core API, Lean tactics, and lean-auto wrapper:

```lean4
import Flex
```

This includes all core types, tactics, elaboration, and the solver.
For lean-smt, additionally import `Flex.Tactic.Oracles.Smt`.

SMTLib-to-Lean is available as an explicit `import Smt2Lean`. It is not imported
by `Flex`. The CHC export, solver, and witness APIs below require `import Flex.CHC`;
automatic integration into `fix` remains a separate step.

To check the dependency integration and existing examples:

```bash
lake build Flex
python3 scripts/regression.py --strict-sorry --jobs 4 --verbose
```

The regression suite includes `Demo/DependencyCompatibility.lean`, which imports
both libraries, parses and reconstructs an SMT definition, and exercises the
existing SMT proof and synthesis routes in the same environment.

## Exporting constraints for CHC solvers

Import `Flex.CHC` to use `Flex.CHC.exportConstraints`. It takes an already peeled
constraint body and its `KVar`s in existential order, and returns an
`ExportedProblem` containing SMT commands, a clause count, and a relation map.
Each map entry preserves the original κ identity and Lean type, its generated
SMT symbol, and its ordered argument sorts, including unused parameters.

```lean
import Flex.CHC

open Lean Meta Qq

run_elab do
  -- An isolated goal for this example; an integrating tactic can use its
  -- existing result from peelKVars instead.
  let goal ← mkFreshExprMVar q(∃ k : Int → Prop,
    k 0 ∧ (∀ x, k x → k (x + 1)) ∧ (∀ x, k x → 0 ≤ x))
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal.mvarId!
  let problem ← Flex.CHC.exportConstraints kvars (← bodyGoal.getType)
  logInfo problem.toSMTLib
```

Run with `lake lean`, which loads the native parser plugin. This produces:

```smt2
(set-logic HORN)
(declare-fun k_0 (Int) Bool)
(assert (k_0 0))
(assert (forall ((v_0 Int)) (=> (k_0 v_0) (k_0 (+ v_0 1)))))
(assert (forall ((v_0 Int)) (=> (k_0 v_0) (<= 0 v_0))))
(check-sat)
```

The exporter reuses Flex's flattening, lean-smt's expression translators and
query builder, and SMTLib-to-Lean's native CHC validator. It neither launches a
solver nor assigns κ witnesses. The script asserts the constraints themselves;
it does not negate a proof goal. Solver-specific options and model requests
belong to the runner described below. The module is an explicit import, so ordinary
`import Flex` does not acquire this native dependency.

The initial fragment supports first-order `Int`, `Bool`, and `Prop` parameters,
Boolean connectives, integer comparisons, addition/subtraction, multiplication
by an integer literal, ordinary `ite`, and local `let` expressions. Standard
arithmetic instances are required. Universal value binders are moved ahead of
guards without capturing variables; unused value binders are omitted because
these types are nonempty. Unused predicate arguments and declarations are kept.
The script groups universal binders in one SMT-LIB `forall`, avoiding Spacer's
rejection of nested mixed Bool/Int binders. Runners should use `toSMTLib` to retain
this formatting.

Inputs must be closed except for the supplied, unassigned κs. Ambient parameters
and hypotheses must occur as explicit binders and guards in the constraint body;
they are never silently turned into existentially interpreted SMT constants.
Nat, other theories, arbitrary function calls, nested quantifiers in guards,
proof-dependent/higher-order constraints, nonlinear products, division/modulo,
and `BEq` comparisons are rejected. Use propositional equality instead of `==`.
SMT Bool represents both Lean Bool and Prop; the relation map retains that
distinction for the witness adapter described below.

The implementation separates the public result types in
[`Types.lean`](Flex/CHC/Types.lean), the allowed theory in
[`Fragment.lean`](Flex/CHC/Fragment.lean), binder and guard preparation in
[`Prepare.lean`](Flex/CHC/Prepare.lean), script formatting in
[`Script.lean`](Flex/CHC/Script.lean), and the export pipeline in
[`Export.lean`](Flex/CHC/Export.lean).
[`Demo/CHC/Export.lean`](Demo/CHC/Export.lean) checks round trips back to Lean,
source scopes and signatures, deterministic output, state preservation, and
unsupported inputs. It runs as part of the standard regression script and does
not require an external solver:

```sh
lake build Demo.CHC.Export
```

## Running Spacer and Eldarica

With `import Flex.CHC`, pass an exported problem to `Flex.CHC.run`. The default
backend is Spacer (`z3` on PATH). Add this after creating `problem` in the
export example above:

```lean
  let result ← Flex.CHC.run problem { backend := .spacer, timeoutMs := 5000 }
  match result.outcome with
  | .sat definitions =>
    for definition in definitions do logInfo definition.text
  | .unsat => logInfo "The exported constraints have no satisfying interpretation."
  | .unknown _ => logInfo "The solver could not decide the constraints."
  | .timedOut => logInfo "The solver exceeded the wall-clock timeout."
  | .error message => throwError message
```

Select Eldarica with the same API:

```lean
  let result ← Flex.CHC.run problem { backend := .eldarica, timeoutMs := 5000 }
  -- An optional executable override accepts a native binary or launcher path:
  let result ← Flex.CHC.run problem {
    backend := .eldarica, executable := some "/path/to/eld", timeoutMs := 5000 }
```

The shared configuration accepts `backend`, an optional `executable` override,
and a positive `timeoutMs` (default `10000`). Without an override, Spacer uses
`z3` and Eldarica uses `eld`, resolved on PATH. The library reads no configuration
environment variables and does not automatically try another backend.
The direct APIs `Flex.CHC.Spacer.run` and `Flex.CHC.Eldarica.run` also remain
available; their backend-specific configurations take a plain executable string.

For the counter example, both solvers return a definition equivalent to
`fun x : Int => 0 ≤ x`. Spacer invokes
`z3 -in -smt2 -model fp.engine=spacer`; Eldarica invokes `eld -in -hsmt -ssol`.
Both use the same serialized Horn script and shared process runner.
Z3's `-model` option produces a model only after `sat`, so `unsat` does not trigger
a failing model request. Eldarica's `-ssol` prints predicate definitions in SMT-LIB
format. `unknown` remains distinct from a wall-clock timeout.

`result.process` retains stdout, stderr, process completion, and elapsed
milliseconds. The deadline covers startup, input, solving, and output collection.
On POSIX systems, a small native adapter uses `posix_spawnp` and pumps all three
pipes concurrently. Timeout or Lean task cancellation kills the process group
directly and reaps the child before returning. Each request starts a fresh solver;
there is no persistent worker, socket, or process registry. Windows retains the
Lean process implementation. No shell command is built from the script or
executable path.

The shared response decoder reuses SMTLib-to-Lean's `SolverResponse.parse`.
It rejects nonzero process exits, solver errors, malformed output, and `sat`
without a model, while accepting an explicitly empty model. Model definitions
remain source text with provenance. The witness API below reconstructs and assigns
them separately. Running either backend leaves Lean goals and witnesses unchanged.
The `fix` tactic integration is planned in PR8.

The implementation separates process handling in
[`Process.lean`](Flex/CHC/Process.lean), shared response handling in
[`Solver.lean`](Flex/CHC/Solver.lean), explicit backend selection in
[`Backend.lean`](Flex/CHC/Backend.lean), and the two adapters in
[`Spacer.lean`](Flex/CHC/Spacer.lean) and [`Eldarica.lean`](Flex/CHC/Eldarica.lean).

The native implementation is isolated in [`native/chc_process.cpp`](native/chc_process.cpp)
behind [`Process/Native.lean`](Flex/CHC/Process/Native.lean). Lake builds and loads
this module automatically using a host C++17 compiler and libc++ (the same
toolchain requirement as lean-cvc5); the rest of Flex's compilation settings
are unchanged.

Run its tests with:

```sh
# Deterministic protocol/process tests (Python 3; no installed solver required).
lake lean Demo/CHC/Runner.lean
lake lean Demo/CHC/Backends.lean
# Real counter, Bool/Int, empty-model, and unsatisfiable cases (requires Z3).
lake lean Demo/CHC/Spacer.lean
```

## Importing and assigning CHC witnesses

After exporting `problem` and running either backend, prepare its complete model with
`importWitnesses`, then explicitly assign the resulting predicates:

```lean
  let result ← Flex.CHC.run problem { backend := .spacer }
  let witnesses ← Flex.CHC.importWitnesses problem result
  -- Inspect witnesses[i].value here; preparation has assigned no κs.
  Flex.CHC.assignWitnesses problem witnesses
  -- The constraint body is still an open proof goal.
```

Each `Witness` stores its solver symbol, original κ metavariable ID, and a closed
Lean expression of the original predicate type. Import matches definitions by
symbol and returns them in existential order, retaining unused arguments and
nullary predicates. Every exported predicate must have a model definition.
Additional model helpers are expanded by SMTLib-to-Lean's existing importer.

The importer represents SMT Bool as Lean Prop. The adapter restores the original
parameter types: a Lean Bool argument `b` is supplied to the imported predicate as
`b = true`, while an original Prop argument is passed unchanged. It checks the
model signature, captured export metadata, current witness-slot type, and adapted
expression. Unsupported model definitions are rejected by the shared importer.

Preparation restores the caller's meta state on both success and failure.
Assignment rechecks the complete witness collection before changing any κ;
missing entries, wrong types, altered identities, and already assigned or
delayed-assigned slots are errors. A failed assignment restores the state from
before the call, including any assignments that were already present.

These checks establish well-typed candidates, not that the predicates satisfy the
constraints. The residual body must still be proved in Lean. Automatic `fix`
integration and fallback are the next step.

[`Witness.lean`](Flex/CHC/Witness.lean) implements these two operations.
[`Demo/CHC/Witness.lean`](Demo/CHC/Witness.lean) tests model adaptation and atomic
assignment without launching a solver. [`Demo/CHC/Instantiate.lean`](Demo/CHC/Instantiate.lean)
tests both solvers through the shared API and closes the resulting constraints with
ordinary Lean proofs, checking that no `sorry` or trusted SMT axiom is used:

```sh
lake lean Demo/CHC/Witness.lean
lake lean Demo/CHC/Instantiate.lean  # requires Z3
CHC_ELDARICA=/path/to/eld lake lean Demo/CHC/Instantiate.lean
```

## Comparing CHC solvers on the demos

[`scripts/benchmark_chc.py`](scripts/benchmark_chc.py) measures the 20 propositions
in `Demo/Basic.lean` and the 8 in `Demo/Cyclic.lean`. The solver paths export the
original constraints, ask Spacer or Eldarica for every predicate, import and
assign their models, then split conjunctions/introduce binders and run `omega`
with `grind` as fallback. They do not invoke Flex's PA, fusion, or zap. Both solvers
use the public `Flex.CHC.run` API and shared witness importer; integration into
the production `fix` tactic is the next step. The benchmark passes `--eldarica`
through its own `CHC_ELDARICA` environment variable to the API's executable override.

```sh
# Z3 and Eldarica must be installed; --eldarica also accepts an absolute path.
python3 scripts/benchmark_chc.py --eldarica eld
# Alternatively, compare only Spacer and the current Flex pipeline.
python3 scripts/benchmark_chc.py --backends fix spacer
```

The baseline is `solve_fixpoint`, including its fusion and PA stages. Both demo
modules are imported for every run, so their qualifier declarations are available
to that baseline. A successful run must produce a closed proof of the original
proposition, pass a kernel check, use only standard Lean axioms, and avoid reusing
the demos' existing proofs. Export, solver, import, and VC failures remain visible
as separate outcomes; `sat` alone does not count as a completed proof.

The script runs serially, with one warm-up and three measured repetitions in a
seeded shuffled order. Timings exclude imports, dependency builds, and witness
pretty printing; they include a fresh solver process, model reconstruction, VC
discharge, and the final proof audit. The solver column measures the complete
adapter call, including startup and response parsing, rather than engine CPU
time. [`eval/CHCCases.lean`](eval/CHCCases.lean) contains the measured pipeline.
Compact per-case medians, individual runs, and environment metadata are written
to `eval/chc_results.csv`, `eval/chc_results_runs.csv`, and
`eval/chc_results.metadata.json`. Failed or incomplete repetition groups have no
speedup entry. The shared exporter currently rejects `ex_nat`, `ex_bool`
(`decide`), `ex_pair`, `ex_prod`, and `ex_userfn` (`double`).

### Native spawning comparison

The macOS arm64 rerun with Lean 4.33.1, Z3 4.15.4, and native Eldarica 2.3
collected all 336 records (one warm-up and three measured repetitions).
The table sums per-case median pipeline times over cases proved in both runs;
it excludes failed cases, imports, and builds. The original results are preserved.

| Demo | Backend | Proved cases | Previous | Native spawn | Speedup |
| --- | --- | ---: | ---: | ---: | ---: |
| Basic | Spacer | 13/20 | 11.234 s | 1.030 s | 10.90× |
| Basic | Eldarica | 15/20 | 13.140 s | 1.365 s | 9.63× |
| Cyclic | Spacer | 8/8 | 7.144 s | 0.639 s | 11.18× |
| Cyclic | Eldarica | 8/8 | 7.129 s | 0.679 s | 10.51× |

Coverage is unchanged: the five export failures remain, and Spacer still fails
VC discharge on `ex14` and `ex_stress`. Median subprocess time across proved
cases dropped from 814 to 16 ms for Spacer and from 818 to 27 ms for Eldarica;
these times include solver execution. A separate `/usr/bin/true` probe using
the previous run's exact source dropped from a 480 ms median to 1 ms.

These are historical comparisons: the unchanged `fix` baseline was 21–28%
slower in the rerun (Basic: 2.226 → 2.700 s; Cyclic: 1.807 → 2.303 s).
Within the new run, both CHC backends prove all eight Cyclic cases about 3.4–3.6×
faster in aggregate than `fix`. For example, `pa6` takes 122 ms with either
solver versus 907 ms with `fix`; Eldarica proves `ex_stress` in 218 ms versus
1326 ms with `fix`. Simple cases can still favor `fix` (`ex1`: 17 ms versus
41/49 ms with Spacer/Eldarica).

See [per-case before/after comparisons](eval/chc_results_posix_comparison.csv),
[new medians](eval/chc_results_posix.csv), [individual runs](eval/chc_results_posix_runs.csv),
and [versions, source hashes, and startup probe](eval/chc_results_posix.metadata.json).
The native runner and all 84 regression files passed the strict `sorry` check.
To reproduce the new run without overwriting the original:

```sh
python3 scripts/benchmark_chc.py --eldarica /path/to/eld --output eval/chc_results_posix.csv
```

### Remaining PRs

PR1–PR7 supplied the dependency integration, export, solver execution, typed
witness reconstruction, and public Spacer/Eldarica selection. The benchmark now
uses that shared API. Native CHC spawning and the initial Demo comparisons are
also implemented. The remaining sequence connects this path to `fix` for the
existing supported fragment; language extensions are tracked separately.

| PR | Deliverable | Completion check |
| --- | --- | --- |
| PR8 | Explicit CHC mode in `fix`: export → solve → reconstruct → assign → prove the original constraints. Restore the entire tactic attempt on failure, including goals, messages, and metavariables. | Existing supported examples produce complete Lean proofs through the tactic; failed attempts leave the original goal intact. |
| PR9 | Configurable fallback between solvers and optionally the existing PA path, with a shared time budget and phase diagnostics. | Unsupported export, missing executable, `unknown`, timeout, bad model, and failed VC discharge follow the configured policy. An explicit CHC-only mode remains available. |
| PR10 | Complete validation and documentation of the public route. Reuse the existing fixtures and benchmark harness; exercise the actual API/tactic, configurations, and failure recovery. | Regression and proof-audit checks pass; reproducible comparisons distinguish CHC-only runs from runs with PA fallback. |
| PR11 | lean-auto native spawning, deferred until the core CHC integration is finished. | A configurable upstream-compatible query hook and Flex adapter pass protocol tests and are measured with the oracle benchmarks; details below. |

A solver's `sat` result supplies candidate witnesses, not a proof. Its `unsat`
result is a synthesis failure, not proof of the existential Lean goal. Every
successful tactic invocation must discharge the original constraints in Lean.

### Planned feature list

These extensions are a separate backlog, not prerequisites for PR7–PR10. They
will receive implementation PRs when selected. The first four items address the
five shared Demo export gaps:

| Capability | Required work | Acceptance case |
| --- | --- | --- |
| Bool/Prop bridge | Support `decide p` and justified Boolean comparisons; basic Bool arguments already work. | `Demo.Basic.ex_bool` |
| Nonrecursive definitions | Controlled unfolding of selected definitions, such as `double x` into `x + x`. | `Demo.Basic.ex_userfn` |
| Nat arithmetic | Encode Nat as Int with nonnegative guards; preserve truncated subtraction; lift imported predicates back through `Int.ofNat`. | `Demo.Basic.ex_nat`, including zero/underflow tests |
| Products and scalar records | Flatten fields into solver arguments; translate constructors, projections, and equality; reconstruct witnesses on the original types. | `Demo.Basic.ex_prod`, `Demo.Basic.ex_pair` |
| More capable VC discharge | Normalize imported quantified predicates and use the configured proof oracle to discharge their constraints. | Spacer's `ex14` and `ex_stress`, which already export and return `sat` |
| Recursive definitions | Encode function calls with graph relations or a supported equivalent, add defining clauses, and connect the inferred predicates to the original Lean function. | Dedicated recursive-function cases, starting with Fibonacci |

Nat and record support need shared argument-encoding metadata: one original Lean
parameter may have a different SMT type or expand into several arguments. Export
and witness reconstruction must use the same map. Reuse the existing SMTLib-to-Lean
Int/Prop importer and selected lean-smt Bool/Nat embedding lemmas.

An acceptance case succeeds only when the solver's candidates lead to a complete,
kernel-checked proof of the original Lean proposition. Evaluate these changes
with the same CHC-only benchmark, keeping PA/fusion/zap out of its solver paths.

Recursive definitions such as Fibonacci remain a separate extension: qualifier
scraping reads equation lemmas, but CHC export also needs graph relations or a
supported equivalent encoding of calls, defining clauses, and Lean proof bridges.
Unfolding a nonrecursive definition does not supply that recursive semantics.

**PR11 — lean-auto native spawning (planned; deferred until PR7–PR10).**
Add a configurable SMT query backend to a pinned lean-auto fork, preserving its
existing implementation as the default. Bind a Flex adapter to the native process
runner, initially for trusted PA synthesis, while keeping certificate generation
on the proof oracle. Account for lean-auto's interactive status-dependent model,
core, and proof requests: the existing batch runner is not a direct replacement
for its live child-process interface. Test protocol outcomes, cancellation,
cleanup, and unchanged proof checks; rerun the oracle benchmarks with phase
timings. Prepare the backend hook and evidence for an upstream contribution.
The current lean-smt tactic already uses in-process cvc5; its performance needs
separate profiling, not this spawning replacement.

## Basic example

```lean4
import Flex

def ex1 : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)
```

See the [`Demo/`](./Demo/Basic.lean) folder for more worked examples.
