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

## λRK frontend: development stage

The STLC upgrade lives separately in [`Flex/VCG/LambdaRK/`](./Flex/VCG/LambdaRK/).
Import `Flex.VCG.LambdaRK` for explicit impredicative System F, parameterized
positive datatypes, pattern matching, structural recursion, and integer-valued
measures. The existing STLC development remains the proof reference.

`LambdaRK.generate signature expression expectedType` validates the signature,
checks the program, and returns its actual `Cstr` tree or an error. Predicate
signatures and recursive refinement templates are explicit; the generator
leaves their unknown predicates for a solver. There is no unrestricted fixpoint.

| Modules | Purpose |
| --- | --- |
| `Syntax`, `Binding`, `SyntaxEqualityLemmas` | Language, binding operations, and proved executable syntax equality |
| `BindingLemmas`, `AlphaLemmas`, `SubstitutionLemmas`, `TypeIndexLemmas` | Syntactic and semantic substitution, capture avoidance, and type-index transport |
| `Signature`, `Context`, `DatatypeSyntax` | Declaration validation, well-formedness, and structural certificates |
| `Semantics`, `Model`, `SemanticTyping` | Evaluation, measures, semantic types, CHC validity, and context/recursion-frame invariants |
| `SemanticsLemmas`, `LogicalLemmas`, `EnvironmentLemmas`, `ContextLemmas` | Determinism, inversion, substitution, and environment/context transport |
| `DatatypeLemmas`, `DatatypeModel`, `DatatypeInterpretation`, `DatatypeAdequacy` | Constructed least-fixed-point datatype interpretation and its adequacy proof |
| `StructuralOrder`, `RecursionLemmas`, `DraftRecursion` | Well-founded descent and semantic structural-recursion rules |
| `Judgments`, `VCGen` | Independent declarative typing and executable constraint generation |
| `DraftBinding`, `DraftContext`, `DraftCore` | Completed proof interfaces and the proved System F core fundamental theorem |
| `DraftTheorems` | Remaining full-language metatheory obligations |

**Full frontend verification remains unfinished.** Exactly three declarations
are still admitted, all in
[`DraftTheorems.lean`](./Flex/VCG/LambdaRK/DraftTheorems.lean): `measure_total`,
`checker_soundness`, and `fundamental_open`. The ordinary frontend umbrella does
not import them. PR7–9's foundation, recursion, and generated-map certificates
have no admitted dependencies; their audits allow only Lean's standard axioms
(`propext`, `Classical.choice`, and `Quot.sound`).

### Revised 15-PR roadmap

These are implementation phases. PR1–9 are implemented locally; the original
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
| 10 | Complete constructor/match and general measure semantic cases, including measure totality and equations. | Next |
| 11 | Prove subtyping-constraint soundness and checker-to-declarative soundness. | Planned |
| 12 | Assemble the full fundamental theorem and generator total correctness. | Planned |
| 13 | Generalize the map-specific lowering/reconstruction bridge; preserve unsupported constraints as residual VCs. | Planned |
| 14 | Close remaining proof debt and audit the full dependency chain. | Planned |
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
[`Foundation.lean`](./Demo/LambdaRK/Foundation.lean) checks the model construction
on one datatype containing both higher-order and polymorphic recursive fields.

PR8 establishes the recursion rules with an induction hypothesis available only
for strictly smaller arguments. Ordinary and type closures retain their lexical
recursion frame. A single proved
[capture regression](./Demo/LambdaRKRecursionChecks.lean) delays a recursive call
under both kinds of closure and invokes them from a caller with no recursion
frame. The System F core theorem and recursion rules have no admitted dependencies;
the combined full-language theorem awaits PR10–12.

PR9 connects the restored Spacer/Eldarica backend to the existing `map` example.
[`MapVC.lean`](./Demo/LambdaRK/MapVC.lean) proves the constructor length equations,
a sound scalar lowering, and exact equality between its raw VC and the actual
`generate signature map mapTy` output. Kernel-reducible syntax comparisons make
that last equality provable; `SyntaxEqualityLemmas` proves the comparisons correct.
[`SolvedMap.lean`](./Demo/LambdaRK/SolvedMap.lean) imports the solver's predicate,
certifies all scalar clauses with Lean, and proves the original generated VC.
It does not supply a handwritten invariant or use trusted SMT axioms.

Both real backends pass: Spacer finds a predicate equivalent to `input = output`;
Eldarica finds `input = output ∧ input ≥ 0`. Individual local pipeline samples
were 97 ms for Spacer (20 ms solver) and 106 ms for Eldarica (37 ms solver).
These are individual measurements, not benchmark averages, and exclude Lean
startup and the separate lowering proof. The lowering is specific to `map`;
PR13 generalizes it. This establishes solver viability, with source-program
correctness still depending on PR11–12.

There are two program examples in [`Demo/LambdaRK.lean`](./Demo/LambdaRK.lean):
polymorphic identity (also instantiated at a polymorphic type), and polymorphic
`map` with a length-preservation specification. `map` generates three nontrivial
clauses: initialization, recursive preservation, and the final length equality.
Focused acceptance/rejection checks live in
[`Demo/LambdaRKChecks.lean`](./Demo/LambdaRKChecks.lean).

```sh
lake build Flex.VCG.LambdaRK Flex.VCG.LambdaRK.DraftTheorems \
  Demo.LambdaRKChecks Demo.LambdaRKRecursionChecks \
  Demo.LambdaRK.Foundation Demo.LambdaRK.ProofAudit Demo.LambdaRK.MapVC
lake lean Demo/LambdaRK/SolvedMap.lean
CHC_ELDARICA=/path/to/eld lake lean Demo/LambdaRK/SolvedMap.lean
```

The initial fragment uses ordered, nonmutual regular datatypes; recursive
occurrences must preserve parameters, and nested recursion is rejected.
Datatype type arguments are invariant. Measures use a restricted definition
language with recursion only on direct recursive fields; its semantic totality
proof is part of PR10. Recursive program calls require smaller pattern-bound
variables. Source binders cannot shadow existing variables, and dependent
arguments and matches use named values (literal arguments are also supported).
Names starting with `$` are reserved. All required theorem dependencies must be
proved before claiming that the full upgrade is verified.
