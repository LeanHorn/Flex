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

> **Note:** This checkout uses Lean 4.33.1 and pins aesop, lean-auto, lean-smt, lean-cvc5, and SMTLib-to-Lean. The restored SMT dependency graph includes mathlib transitively.

---

## Importing

Import the core framework with:

```lean4
import Flex
```

This includes the core types, tactics, elaboration, and predicate abstraction.
Import `Flex.CHC` separately for Spacer/Eldarica integration.

### Example

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

## Spacer and Eldarica

Import `Flex.CHC` for the shared `Flex.CHC.solveGoal` API. It exports a supported
existential Horn goal, runs the selected backend, imports predicate witnesses,
and checks the instantiated clauses in Lean. Results distinguish a solved goal,
instantiated witnesses with residual obligations, and a failed attempt with
restored elaborator state. The library does not change `fix` or add a `flex` tactic.

The default backend is Spacer (`z3` on PATH). Select Eldarica with
`{ backend := .eldarica }`, using `eld` on PATH, or supply `executable := some path`.
Both use the native `posix_spawn` runner on macOS/Linux, with a fresh process and
wall-clock timeout per request. The portable fallback uses `IO.Process`.

The implementation and regressions are under [`Flex/CHC/`](./Flex/CHC/) and
[`Demo/CHC/`](./Demo/CHC/). To exercise real solver-to-Lean reconstruction:

```sh
lake build Flex.CHC
lake lean Demo/CHC/Instantiate.lean
CHC_ELDARICA=/path/to/eld lake lean Demo/CHC/Instantiate.lean
```

## SystemFRK frontend

Import `Flex.VCG.SystemFRK` for the mechanization of explicit impredicative
System F, positive parameterized datatypes, refinements, pattern matching,
structural recursion, and integer-valued measures.

[`generated_total_correctness`](./Flex/VCG/SystemFRK/Correctness.lean) proves that
successful generation and validity of the returned constraints imply evaluation
to a value satisfying the expected semantic type. The datatype interpretation
is constructed as a least fixed point; model adequacy is proved, not assumed by
the final theorem. Recursive calls use a well-founded strict-subvalue ordering.

Arrow interpretations require an ordinary or recursive closure, including for
empty domains. `HasType.wellFormed` establishes full result formation for every
typing derivation. The generator checks intermediate result types after
substitution; logical equality distinguishes abstract type variables before
instantiation. Type binders have lexical scope, while expression binders remain
subject to the no-shadowing restriction.

Lambda checking retains the expected input refinements while checking annotation
compatibility. Invariant datatype arguments compare modulo alpha-equivalence,
with a proof that successful comparison preserves their interpretation. Datatype
binders retain definedness of their declared measures in the generated constraints;
the soundness proof derives these facts from measure totality. The final
`generated_total_correctness` theorem needs no additional assumptions. This is
a targeted completeness improvement, not a claim of full verifier completeness.

| Mechanization | Contents |
| --- | --- |
| [`Syntax.lean`](./Flex/VCG/SystemFRK/Syntax.lean), [`Binding/`](./Flex/VCG/SystemFRK/Binding/) | Grammar, capture-avoiding substitution, freshness, and scope |
| [`Semantics.lean`](./Flex/VCG/SystemFRK/Semantics.lean), [`Model.lean`](./Flex/VCG/SystemFRK/Model.lean) | Evaluation, semantic types, and constraint validity |
| [`Datatypes/`](./Flex/VCG/SystemFRK/Datatypes/) | Positive fixed-point interpretation and constructor adequacy |
| [`Judgments.lean`](./Flex/VCG/SystemFRK/Judgments.lean), [`Typing/`](./Flex/VCG/SystemFRK/Typing/) | Independent declarative typing and the fundamental theorem |
| [`VCGen.lean`](./Flex/VCG/SystemFRK/VCGen.lean), [`Generator/`](./Flex/VCG/SystemFRK/Generator/) | Executable generation and checker soundness |
| [`Bridge/`](./Flex/VCG/SystemFRK/Bridge/) | Optional scalar lowering and checked solver certificates |

The proof chain is `Generator/Soundness` → `Typing/Fundamental` → `Correctness`,
using `Datatypes/Adequacy`. The optional `Flex.VCG.SystemFRK.Bridge` import
provides `systemfrk_chc` and `Bridge.solveGoal` for proving generated constraints.
External solvers supply predicate candidates; Lean checks scalar certificates,
their implications to source clauses, and assembly of the original constraint.
Unsupported source clauses remain explicit proof obligations.

All demos live in **[`Demo/SystemFRK.lean`](./Demo/SystemFRK.lean)**:

| # | Example | Mechanized result |
| --- | --- | --- |
| 1 | Polymorphic identity | Total correctness and identity application for every integer |
| 2 | Impredicative identity | Identity instantiated at a polymorphic type |
| 3 | Polymorphic composition | Higher-order functions under three type binders |
| 4 | Dependent application | Capture avoidance and evaluation to the original argument |
| 5 | Singleton list | Constructor typing and a length-one refinement |
| 6 | Structural `map` | Solver-inferred invariant, total correctness, and execution with the correct length on every finite integer list |
| 7 | Weighted recursive measure | Integer fields and recursive tails establish an exact result |
| 8 | Higher-order datatypes | Inhabited positive recursive function and polymorphic fields |
| 9 | Delayed recursion | Calls retain lexical recursion through ordinary and type closures |
| 10 | False specification | A generated false VC is refuted; false refinements and stuck applications cannot be certified |

Each successful example proves its generation equation and constraint validity
before applying the public correctness theorem. The file also audits transitive
axiom dependencies of the imported SystemFRK proofs and its examples, permitting
only `propext`, `Classical.choice`, and `Quot.sound`.

```sh
lake build Flex.VCG.SystemFRK
lake lean Demo/SystemFRK.lean
# Optional: run the map certificate with Eldarica instead of Z3/Spacer.
CHC_ELDARICA=/path/to/eld lake lean Demo/SystemFRK.lean
```

Use `lake lean` to load the native libraries needed by the solver certificate.
Z3 must be on PATH unless `CHC_ELDARICA` selects an Eldarica executable.

The verified fragment uses ordered, nonmutual regular datatypes with unchanged
recursive parameters and invariant type arguments. Nested recursion is rejected.
Measures recurse on direct recursive fields; program recursion requires smaller
pattern-bound variables. Source binders cannot shadow existing variables.
Dependent arguments and matches use named values (literal arguments are also
supported), and `$` names are reserved. The solver bridge handles scalar
observations; arbitrary datatype, function, and polymorphic values remain in
source proof obligations.
