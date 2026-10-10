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

## Running Spacer

With `import Flex.CHC` and `z3` on PATH, pass an exported problem to
`Flex.CHC.Spacer.run`. For example, add this after creating `problem` in the
export example above:

```lean
  let result ← Flex.CHC.Spacer.run problem { timeoutMs := 5000 }
  match result.outcome with
  | .sat definitions =>
    for definition in definitions do logInfo definition.text
  | .unsat => logInfo "The exported constraints have no satisfying interpretation."
  | .unknown _ => logInfo "Spacer could not decide the constraints."
  | .timedOut => logInfo "Spacer exceeded the wall-clock timeout."
  | .error message => throwError message
```

For the counter example, Spacer returns a definition equivalent to
`fun x : Int => 0 ≤ x`. The configuration accepts `executable` (default `"z3"`)
and a positive `timeoutMs` (default `10000`). The runner invokes
`z3 -in -smt2 -model fp.engine=spacer` directly, using one process and one solve.
Z3's `-model` option produces a model only after `sat`, so `unsat` does not trigger
a failing model request. `unknown` remains distinct from a wall-clock timeout.

`result.process` retains stdout, stderr, process completion, and elapsed
milliseconds. The deadline covers input, solving, and output collection. On
POSIX systems, cancellation terminates the solver's process group; after a
200 ms grace period, `/bin/kill` supplies SIGKILL if needed. Cleanup reaps the
child and joins the pipe readers before returning. No shell command is built
from the script or executable path.

The shared response decoder reuses SMTLib-to-Lean's `SolverResponse.parse`.
It rejects nonzero process exits, solver errors, malformed output, and `sat`
without a model, while accepting an explicitly empty model. Model definitions
remain source text with provenance. The witness API below reconstructs and assigns
them separately. Running Spacer does not close a Lean goal or add a `fix` option.

The implementation separates process handling in
[`Process.lean`](Flex/CHC/Process.lean), shared response handling in
[`Solver.lean`](Flex/CHC/Solver.lean), and the backend adapter in
[`Spacer.lean`](Flex/CHC/Spacer.lean). Run its tests with:

```sh
# Deterministic protocol/process tests (Python 3; no Z3 required).
lake lean Demo/CHC/Runner.lean
# Real counter, Bool/Int, empty-model, and unsatisfiable cases (requires Z3).
lake lean Demo/CHC/Spacer.lean
```

## Importing and assigning CHC witnesses

After exporting `problem` and running Spacer, prepare its complete model with
`importWitnesses`, then explicitly assign the resulting predicates:

```lean
  let result ← Flex.CHC.Spacer.run problem
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
tests the full Spacer-to-witness path and closes the resulting constraints with
ordinary Lean proofs, checking that no `sorry` or trusted SMT axiom is used:

```sh
lake lean Demo/CHC/Witness.lean
lake lean Demo/CHC/Instantiate.lean  # requires Z3
```

## Comparing CHC solvers on the demos

[`scripts/benchmark_chc.py`](scripts/benchmark_chc.py) measures the 20 propositions
in `Demo/Basic.lean` and the 8 in `Demo/Cyclic.lean`. The solver paths export the
original constraints, ask Spacer or Eldarica for every predicate, import and
assign their models, then split conjunctions/introduce binders and run `omega`
with `grind` as fallback. They do not invoke Flex's PA, fusion, or zap. Eldarica
is invoked through a benchmark adapter using the shared process runner and model
importer; it is not yet a production `fix` backend.

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
