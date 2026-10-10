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
by `Flex` and does not change `fix` or add CHC invariant synthesis yet.

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
distinction for the later witness-instantiation adapter.

The implementation separates the public result types in
[`Types.lean`](Flex/CHC/Types.lean), the allowed theory in
[`Fragment.lean`](Flex/CHC/Fragment.lean), binder and guard preparation in
[`Prepare.lean`](Flex/CHC/Prepare.lean), script formatting in
[`Script.lean`](Flex/CHC/Script.lean), and the export pipeline in
[`Export.lean`](Flex/CHC/Export.lean).
[`Demo/CHCExport.lean`](Demo/CHCExport.lean) checks round trips back to Lean,
source scopes and signatures, deterministic output, state preservation, and
unsupported inputs. It runs as part of the standard regression script and does
not require an external solver:

```sh
lake build Demo.CHCExport
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
remain source text with provenance; reconstructing, type-checking, and assigning
them as Lean witnesses belongs to the next integration step. This API does not
close a Lean goal or add a `fix` option yet.

The implementation separates process handling in
[`Process.lean`](Flex/CHC/Process.lean), shared response handling in
[`Solver.lean`](Flex/CHC/Solver.lean), and the backend adapter in
[`Spacer.lean`](Flex/CHC/Spacer.lean). Run its tests with:

```sh
# Deterministic protocol/process tests (Python 3; no Z3 required).
lake lean Demo/CHCRunner.lean
# Real counter, Bool/Int, empty-model, and unsatisfiable cases (requires Z3).
lake lean Demo/CHCSpacer.lean
```

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
