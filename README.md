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
