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

The STLC upgrade lives separately in [`Flex/VCG/SystemFRK/`](./Flex/VCG/SystemFRK/).
Import `Flex.VCG.SystemFRK` for explicit impredicative System F, parameterized
positive datatypes, pattern matching, structural recursion, and integer-valued
measures. The existing STLC development remains the proof reference.

`SystemFRK.generate signature expression expectedType` validates the signature,
checks the program, and returns its actual `Cstr` tree or an error. Predicate
signatures and recursive refinement templates are explicit; the generator
leaves their unknown predicates for a solver. There is no unrestricted fixpoint.

Read the definitions in this order:

1. [`Syntax.lean`](./Flex/VCG/SystemFRK/Syntax.lean) and [`Binding.lean`](./Flex/VCG/SystemFRK/Binding.lean): grammar, binder conventions, and substitution.
2. [`Semantics.lean`](./Flex/VCG/SystemFRK/Semantics.lean) and [`Model.lean`](./Flex/VCG/SystemFRK/Model.lean): evaluation, semantic types, and constraint validity.
3. [`Signature.lean`](./Flex/VCG/SystemFRK/Signature.lean), [`Context.lean`](./Flex/VCG/SystemFRK/Context.lean), and [`Judgments.lean`](./Flex/VCG/SystemFRK/Judgments.lean): declaration checks, formation, and declarative typing.
4. [`SemanticTyping.lean`](./Flex/VCG/SystemFRK/SemanticTyping.lean): the logical relation and its context/recursion invariants.
5. [`VCGen.lean`](./Flex/VCG/SystemFRK/VCGen.lean) and [`Correctness.lean`](./Flex/VCG/SystemFRK/Correctness.lean): executable generator and end-to-end guarantee.

Supporting developments are grouped by topic; declaration names remain in `SystemFRK`.

| Directory | Contents |
| --- | --- |
| `Binding/` | Syntax equality, freshness, renaming, substitution, and environment transport |
| `Datatypes/` | Formation certificates, positive fixed-point model, and adequacy |
| `Semantics/` | Evaluation determinism, structural descent, and measure totality |
| `Typing/` | Context transport, semantic typing rules, and the full fundamental theorem |
| `Generator/` | Constraint entailment, subtyping, and synthesis/checking soundness |
| `Bridge/` | Optional checked lowering, solver orchestration, and residual goals |

The main proof chain is `Generator/Soundness` → `Typing/Fundamental` →
`Correctness`, using the model from `Datatypes/Adequacy`. The optional bridge
proves validity of the generated constraints; the language proofs do not import it.

**The retained SystemFRK language now has a proved total-correctness theorem.**
`generated_total_correctness` states that successful generation and validity of
its returned CHCs imply evaluation to a value satisfying the expected semantic
type, using the constructed datatype interpretation. No model-existence,
checker-soundness, or termination premise is left unproved. The transitive axiom audit permits only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.

The reusable solver bridge is available through the optional
`Flex.VCG.SystemFRK.Bridge` import. It derives scalar clauses from a closed source
VC and checks their connection to its original semantics before invoking
Spacer/Eldarica. The core language metatheory remains independent of this import.

### Revised 15-PR roadmap

These are implementation phases. PR1–14 are implemented locally; the original
partial binding interfaces have now been proved as part of PR7.

| PR | Concrete result | Status |
| --- | --- | --- |
| 1 | Define the target calculus, semantics, typing specification, and main theorem statements. | Implemented scaffold |
| 2 | Implement checking and CHC generation; run identity and length-preserving `map`. | Implemented |
| 3 | Establish binding/substitution contracts and prove the straightforward lemmas. | Complete; deferred proofs closed in PR7 |
| 4 | Define open semantic typing with explicit context, recursion-frame, and decrease invariants. | Complete |
| 5 | Prove evaluation/measure determinism and semantic inversion lemmas. | Proved |
| 6 | Prove the fundamental theorem for the System F expression core. | Proved; binding/context dependencies closed in PR7 |
| 7 | Complete required binding/context proofs, audit capture and scope, and construct an adequate datatype model. | Proved and audited |
| 8 | Prove structural descent and semantic recursion rules; check recursion captured inside ordinary and polymorphic closures. | Proved and audited |
| 9 | Lower the actual generated `map` VC, synthesize an invariant with Spacer/Eldarica, and prove the original VC in Lean. | Both real backends pass |
| 10 | Complete constructor/match and general measure semantic cases, including measure totality and equations. | Proved and audited |
| 11 | Prove subtyping-constraint soundness and checker-to-declarative soundness. | Proved and audited |
| 12 | Assemble the full fundamental theorem and generator total correctness. | Proved and audited |
| 13 | Generalize the map-specific lowering/reconstruction bridge; preserve unsupported constraints as residual VCs. | Implemented; both real backends pass |
| 14 | Consolidate compatibility modules, close any proof debt introduced by PR13, and audit the full dependency chain. | Consolidated and audited |
| 15 | Deliver verified versions of the same two examples, final checks, and documentation. | Planned |

PR7 proves the open-substitution contracts, including replacements with free
logical names. Binder freshening protects the reserved refinement witness
`$value`; semantic equality uses alpha-renaming and environment agreement.
The scope audit also adds the missing outer-context scope premise to the match
rule, preventing pattern-local names from escaping in its result type.

Datatype interpretations are constructed as least fixed points in declaration
order. Their adequacy includes positive recursive occurrences under function
codomains and polymorphic fields. Signature validation and type formation now
record structural certificates after their existing detailed checks, giving
proofs direct access to positivity, declaration ordering, and scope facts.
This adds a structural pass while retaining the original diagnostics.
[`Foundation.lean`](./Demo/SystemFRK/Foundation.lean) checks the model construction
on one datatype containing both higher-order and polymorphic recursive fields.

PR8 establishes the recursion rules with an induction hypothesis available only
for strictly smaller arguments. Ordinary and type closures retain their lexical
recursion frame. A single proved
[capture regression](./Demo/SystemFRKRecursionChecks.lean) delays a recursive call
under both kinds of closure and invokes them from a caller with no recursion
frame. These results now participate in the full-language fundamental theorem.

PR9 connects the restored Spacer/Eldarica backend to the existing `map` example.
[`MapVC.lean`](./Demo/SystemFRK/MapVC.lean) records a readable raw VC and proves
its exact equality with the actual `generate signature map mapTy` output. The
reusable bridge now derives measure equations and scalar clauses from that VC.
Kernel-reducible syntax comparisons make
that last equality provable; `Binding/Equality` proves the comparisons correct.
[`SolvedMap.lean`](./Demo/SystemFRK/SolvedMap.lean) imports the solver's predicate,
certifies all scalar clauses with Lean, and proves the original generated VC.
It does not supply a handwritten invariant or use trusted SMT axioms.

Both real backends pass: Spacer finds a predicate equivalent to `input = output`;
Eldarica finds `input = output ∧ input ≥ 0`. PR9's individual local pipeline samples
were 97 ms for Spacer (20 ms solver) and 106 ms for Eldarica (37 ms solver).
These are individual measurements, not benchmark averages, and exclude Lean
startup and the separate lowering proof. They describe the original PR9 path,
not timings of the generalized bridge. `SolvedMap.map_total_correct` now derives
the source program's full semantic specification from the generic solver bridge
and PR11–12's correctness theorem.

PR10 proves constructor and branch evaluation, field-environment transport,
constructor equations, and strict decrease through nested patterns. Measures
terminate on typed datatype values and satisfy their defining equations.
Signature validation records constructor uniqueness and executable measure
coverage/body certificates after its original diagnostic checks.

PR11 proves subtyping locally from the emitted constraints, including dependent
function contravariance, polymorphism, and outer refinements. Synthesis and
checking soundness are proved together by fuel induction against the independent
`HasType` rules. The proof exposed missing scope evidence: pattern rules now
require scoped datatype arguments, each successful synthesis branch checks its
result scope, and recursive checking validates expected-type scope. Generated
subtyping witnesses avoid names already occurring in either type. Field and
branch traversals use small helpers shared with their correctness arguments.

PR12 combines those proofs with the full open fundamental theorem. The ordinary
`Flex.VCG.SystemFRK` import exposes
[`generated_total_correctness`](./Flex/VCG/SystemFRK/Correctness.lean), which
constructs the datatype model and requires only successful generation and valid
returned constraints. The solver-backed `map_total_correct` theorem and its
axiom audit exercise this full dependency chain with both backends.

PR13 replaces the hand-built scalar problem in `SolvedMap` with the reusable
[`Bridge.solveGoal`](./Flex/VCG/SystemFRK/Bridge/Goal.lean) API. For a goal of the
form `∃ κ, vc.Valid signature κ`, `systemfrk_chc` uses Spacer; use
`systemfrk_chc eldarica` or `systemfrk_chc eldarica "/path/to/eld"` for Eldarica.
The signature and VC must be closed Lean terms. Their executable reflection is
checked by kernel conversion against those original terms.

The supported solver fragment has these boundaries:

- Multiple predicates may have different mixtures of `Int` and `Bool` arguments.
  Scalar clauses support literals, addition, equality, inequalities, and Boolean
  combinations. Scalar quantifiers retain their declared sorts.
- Constructor equalities in guards supply aliases. Declared measure equations
  expand known constructors using literals, integer fields, addition, and direct
  recursive-field observations. A measure of an arbitrary runtime value needs
  evaluation evidence from a positive guard; it is never assumed total merely
  because a scalar variable could represent its result.
- Each proposed scalar clause must imply its exact source clause, proved in Lean
  with abstract predicates. Some unsupported guards can be dropped to obtain a
  stronger scalar obligation, but the same implication check still applies.
  Failed lowering or proof reconstruction retains the original clause.
- Solver predicates are instantiated even when certification leaves work. The
  remaining scalar or source obligations are ordinary Lean goals. Source
  residuals retain their original clause indices; scalar certificate indices
  live separately in `report.solver`, since normalization may split clauses.
  Runtime-`Value` predicate
  arguments and unused predicate declarations remain explicit witness goals;
  they are not encoded as SMT datatypes or higher-order solver arguments.

The flattening theorem, per-clause implications, and solver certificates compose
into a proof of the original VC. Completed and partial scaffolds are checked for
admitted proofs and trusted SMT dependencies. Backend failure restores the entry
state. [`BridgeChecks.lean`](./Demo/SystemFRK/BridgeChecks.lean) exercises mixed
sorts, multiple predicates, partial results, and failure rollback independently
of `map`; [`BridgeReconstruction.lean`](./Demo/SystemFRK/BridgeReconstruction.lean)
checks that undefined measures remain explicit residual obligations.

The old `Draft*` compatibility modules and staged core-only theorem have been
removed. The full fundamental theorem is the single correctness interface for
all expression forms. Imports of internal modules now follow the directory table
above; the public `Flex.VCG.SystemFRK` and `Flex.VCG.SystemFRK.Bridge` imports are unchanged.

The expanded [`ProofAudit.lean`](./Demo/SystemFRK/ProofAudit.lean) discovers the
production logical declarations, including private lemmas and the bridge's
semantic reconstruction laws, and checks their transitive axiom dependencies.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Separate
interface checks retain the intended assumptions of the principal theorems:

| Boundary | Required evidence | Result |
| --- | --- | --- |
| Executable generator → declarative typing | Successful generation and validity of its returned VC | A derivation in the independent `HasType` rules |
| Declarative typing → execution | Valid signature, adequate model, and typed expression | Termination with a value in the semantic type |
| Generated program → total correctness | Successful generation and VC validity | The preceding execution guarantee with the constructed datatype model |
| Scalar solver → original VC | Checked lowering implications, imported predicates, and completed certificates | Validity of the original source constraint |

The bridge's native syntax evaluation and external solvers supply candidates;
kernel conversion and ordinary Lean proofs check their contribution. A partial
result still requires its explicit goals to be proved. The regression checks also
ensure that reusing an already assigned goal fails without replacing its proof,
and that native evaluation disagreeing with kernel reduction is rejected at the
syntax-reflection boundary.

There are two program examples in [`Demo/SystemFRK.lean`](./Demo/SystemFRK.lean):
polymorphic identity (also instantiated at a polymorphic type), and polymorphic
`map` with a length-preservation specification. `map` generates three nontrivial
clauses: initialization, recursive preservation, and the final length equality.
Focused acceptance/rejection checks live in
[`Demo/SystemFRKChecks.lean`](./Demo/SystemFRKChecks.lean).

```sh
lake build Flex.VCG.SystemFRK \
  Demo.SystemFRKChecks Demo.SystemFRKRecursionChecks \
  Demo.SystemFRK.Foundation Demo.SystemFRK.SoundnessChecks \
  Demo.SystemFRK.ProofAudit Demo.SystemFRK.MapVC \
  Flex.VCG.SystemFRK.Bridge Demo.SystemFRK.BridgeLowering \
  Demo.SystemFRK.BridgeQuote Demo.SystemFRK.BridgeReconstruction
lake lean Demo/SystemFRK/SolvedMap.lean
CHC_ELDARICA=/path/to/eld lake lean Demo/SystemFRK/SolvedMap.lean
lake lean Demo/SystemFRK/BridgeChecks.lean
CHC_ELDARICA=/path/to/eld lake lean Demo/SystemFRK/BridgeChecks.lean
```

The initial fragment uses ordered, nonmutual regular datatypes; recursive
occurrences must preserve parameters, and nested recursion is rejected.
Datatype type arguments are invariant. Measures use a restricted definition
language with recursion only on direct recursive fields, whose totality is proved. Recursive program calls require smaller pattern-bound
variables. Source binders cannot shadow existing variables, and dependent
arguments and matches use named values (literal arguments are also supported).
Names starting with `$` are reserved. Solver support remains narrower than the
verified source language: the bridge projects supported scalar observations;
arbitrary datatype, function, and polymorphic values remain in source obligations.
