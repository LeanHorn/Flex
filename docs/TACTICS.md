# Flex tactics — reference

One paragraph and one minimal example per user-facing tactic. Tactics live in [Flex/Tactic/](../Flex/Tactic/); all are re-exported through `import Flex.Tactic`.

---

## 1. Constraint solvers

### `zap`
Source: [Tactics/Zap.lean](../Flex/Tactic/Tactics/Zap.lean). Peels every `∃ κᵢ`, classifies the κ's as *acyclic* / *cyclic*, eliminates the acyclic ones via `sol1 + elim*` and emits a bridge term `λ h. Exists.elim … (nav …)`. Residual obligations from the elimination are exposed alongside a new main goal of the form `∃ <cyclic κ's>, c′`. Acyclic-only inputs collapse to pure leaf obligations.

```lean
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x → ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  zap
  all_goals first | rfl | grind
```

### `solve_fixpoint`
Source: [Tactics/SolveFixpoint.lean:189](../Flex/Tactic/Tactics/SolveFixpoint.lean#L189). Superset of `zap`: assigns acyclic κ-mvars via `sol1 + elim*`, then runs **predicate abstraction** on the cyclic κ's, drawing qualifiers from `@[qualif]`-tagged declarations. Any κ left unassigned is exposed as a user goal; the residual proof obligation is dispatched with an internal `intro/and_intros/native_decide/grind/aesop/omega/bv_decide/constructor+grind` close-loop.

```lean
@[qualif] def q_nonneg : Qualif := fun ν => ν ≥ 0

example : ∃ κ : Int → Prop,
    (∀ x, x ≥ 0 → κ x) ∧
    (∀ a, κ a → κ (a + 1)) ∧
    (∀ b, κ b → b ≥ 0) := by
  solve_fixpoint      -- κ := fun a => a ≥ 0  (via PA on the cyclic κ)
```

### `solK1 [κ]`
Source: [Tactics/Sol1.lean:160](../Flex/Tactic/Tactics/Sol1.lean#L160). Solves exactly one acyclic κ in the goal's `∃`-chain and binds its witness as a `let`-decl named after the binder. Without an argument, picks the first acyclic κ whose `sol1` witness is closed (no references back to other scratch κ-mvars). With `solK1 κᵢ`, targets that κ specifically — `perm_exists` is used to permute it to the outermost `∃` first. The remaining `∃`-chain is preserved; the solved κ continues to appear in the goal by *name* and can be inlined on demand with `lazy_unfold`.

```lean
def ex : Prop :=
  ∃ κ₁ κ₂ : Int → Prop,
    ∀ x : Int, (∀ ν, ν = x + 1 → κ₁ ν) ∧ (∀ ν, ν = x - 1 → κ₂ ν)

example : ex := by
  unfold ex
  solK1 κ₂            -- κ₂ : Int → Prop := …  ; goal still ∃ κ₁, …
  solK1 κ₁
  lazy_unfold κ₁ κ₂
  grind
```

### `rewriteKs`
Source: [Tactics/RewriteKs.lean:129](../Flex/Tactic/Tactics/RewriteKs.lean#L129). Reorders the head `∃`-chain into the order the elimination solvers expect (cyclic κ's first, then acyclic in topological / sinks-first order). Discharges the resulting `Iff` via `perm_exists`.

```lean
example : ∃ κ₁ κ₂ : Int → Prop,            -- κ₂ is a sink
    (∀ x, κ₁ x → κ₂ (x+1)) ∧ (∀ y, κ₂ y → y ≥ 0) := by
  rewriteKs            -- goal now: ∃ κ₂ κ₁, …  (sink first)
  zap
```

### `perm_exists`
Source: [Tactics/RewriteKs.lean:55](../Flex/Tactic/Tactics/RewriteKs.lean#L55). Proves `(∃ x₀ … xₙ, P) ↔ (∃ y₀ … yₙ, P)` (or its `→` form) when both sides have the same body and binder names match modulo permutation.

```lean
example : (∃ x y, x + y = 0) ↔ (∃ y x, x + y = 0) := by
  perm_exists
```

---

## 2. Existential manipulation

### `name_witness <term>`
Source: [Tactics/Lazy.lean:12](../Flex/Tactic/Tactics/Lazy.lean#L12). For a goal `∃ κ : T, …`, introduces a `let κ : T := <term>` and discharges the `∃` with it. Binder name is read off the goal. Chain for nested `∃`'s.

```lean
example : ∃ κ : Int → Prop, ∀ x, x ≥ 0 → κ (x + 1) := by
  name_witness fun ν => ∃ x, x ≥ 0 ∧ ν = x + 1
  intro x hx; exact ⟨x, hx, rfl⟩
```

### `lazy_unfold k₁ k₂ …`
Source: [Tactics/Lazy.lean:35](../Flex/Tactic/Tactics/Lazy.lean#L35). Unfolds the named local `let`-bindings throughout goal and hypotheses **only at this proof position** (β-reduces against the spine, recurses into the result). Anywhere else the let stays folded.

```lean
example (κ := fun ν : Int => ν ≥ 0) : (∀ x, x ≥ 5 → κ x) := by
  lazy_unfold κ       -- goal becomes  ∀ x, x ≥ 5 → x ≥ 0
  intro x hx; omega
```

### `hoist_exists`
Source: [Tactics/Hoist.lean:152](../Flex/Tactic/Tactics/Hoist.lean#L152). Pulls every `∃` to the head of the goal via `and_exists_hoist`, `exists_and_hoist`, `reorder_exists`, then restores the original binder names.

```lean
example : (∀ x, ∃ y, x + y = 0) → ∃ f, ∀ x, x + f x = 0 := by
  intro h; hoist_exists; exact h
```

### `under_exists => <tacs>`
Source: [Tactics/Hoist.lean:171](../Flex/Tactic/Tactics/Hoist.lean#L171). Replaces every head `∃`-witness with a fresh mvar, runs `<tacs>` on the now-flat body. Solved subgoals determine the witnesses; remaining Prop subgoals are re-wrapped as a `∧`-conjunction under any still-undetermined witnesses (extracted via `Classical.choose`).

```lean
example : ∃ x : Nat, x + 1 = 4 ∧ x > 0 := by
  under_exists =>
    refine ⟨?_, ?_⟩  -- both subgoals constrain the same witness
    · rfl            -- forces x = 3
    · decide
```

### `trivialk`
Source: [Tactics/Zap.lean:72](../Flex/Tactic/Tactics/Zap.lean#L72). For a head `∃ f : t₁ → … → tₙ → Prop, P f` (n ≥ 1), supplies `fun _ _ … _ => True` as the witness and recurses while the goal stays of that shape.

```lean
example : ∃ κ : Int → Int → Prop, ∀ a b, κ a b ∨ ¬ κ a b := by
  trivialk            -- κ := fun _ _ => True
  intro a b; left; trivial
```

### `elimT`
Source: [Tactics/Zap.lean:75](../Flex/Tactic/Tactics/Zap.lean#L75). Shorthand for `trivialk; simp; zap`. Useful when the κ's of a goal are all unconstrained — kills them with the trivial witness and finishes.

```lean
example : ∃ κ : Int → Prop, ∀ x, x = x → κ x ∨ True := by elimT
```

---

## 3. Goal & hypothesis decomposition

### `zap`
Source: [Tactics/Zap.lean:34](../Flex/Tactic/Tactics/Zap.lean#L34). Recursively introduces `∀`/`→` and splits `∧`. At each leaf goal tries `grind`, then `rfl`. Skips leaves it cannot close and restores them after siblings.

```lean
example (P Q : Nat → Prop) (h : ∀ x, P x ∧ Q x) : ∀ x, P x ∧ Q x := by
  zap                 -- intros x, splits ∧, closes both halves via grind
```

### `zapTrue`
Source: [Tactics/Zap.lean:200](../Flex/Tactic/Tactics/Zap.lean#L200). Recurses under `∃`/`∧`/`∀`(`→`), replaces every `grind`-provable leaf proposition with `True`, then cleans up with `simp only [and_true, true_and]`.

```lean
example (P : Int → Prop) : ∃ x, x > 100 ∧ 4 > 2 ∧ P x := by
  zapTrue             -- goal becomes  ∃ x, x > 100 ∧ P x
  sorry
```

### `flatten_and_solve_leafs (<tac>)`
Source: [Tactics/Zap.lean:202](../Flex/Tactic/Tactics/Zap.lean#L202). Repeatedly applies, in any goal: `intro`, `And.intro`, or the user-supplied `<tac>`. Useful when you want a custom closer at the leaves.

```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q ∧ (P ∧ Q) := by
  flatten_and_solve_leafs (assumption)
```

### `leafClosers`
Source: [Closers.lean:14](../Flex/Tactic/Closers.lean#L14). `first | omega | grind | native_decide | bv_decide | (constructor <;> grind) | aesop`. Extend by editing the macro.

```lean
example (n : Nat) : n + 0 = n ∧ n * 1 = n := by leafClosers
```

### `split_hyp_ands [n]`, `split_hyp_ors [n]`, `split_hyp_exists [n]`
Source: [Tactics/SplitHyps.lean:56](../Flex/Tactic/Tactics/SplitHyps.lean#L56), [Tactics/SplitHyps.lean:164](../Flex/Tactic/Tactics/SplitHyps.lean#L164), [Tactics/SplitHyps.lean:262](../Flex/Tactic/Tactics/SplitHyps.lean#L262). One pass over the context, destructuring (via `rcases` / `cases`) every hypothesis of the given shape; optional bound limits the number of passes. Each throws a typed error if nothing matched (so they compose under `first | …`).

```lean
example (P Q R : Prop) (h : (P ∧ Q) ∧ R) : R := by
  split_hyp_ands; assumption

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  split_hyp_ors <;> (first | (left; assumption) | (right; assumption))

example (P : Nat → Prop) (h : ∃ x, P x) : ∃ y, P y := by
  split_hyp_exists; exact ⟨_, by assumption⟩
```

### `split_hyp_and_exist`
Source: [Tactics/SplitHyps.lean:314](../Flex/Tactic/Tactics/SplitHyps.lean#L314). `repeat (first | split_hyp_ands | split_hyp_exists)`. No `∨`-forking — useful when you want a single goal after destructuring.

```lean
example (P Q R : Nat → Prop) (h : ∃ x, P x ∧ Q x ∧ R x) : True := by
  split_hyp_and_exist; trivial
```

### `split_hyps`
Source: [Tactics/SplitHyps.lean:319](../Flex/Tactic/Tactics/SplitHyps.lean#L319). Same, but also `∨` and runs across **all** goals: `repeat (any_goals (first | split_hyp_ands | split_hyp_ors | split_hyp_exists))`.

```lean
example (P Q R : Nat → Prop) (h : ∃ x, P x ∧ (Q x ∨ R x)) :
    ∃ y, P y ∧ (R y ∨ Q y) := by
  split_hyps
  · exact ⟨_, by assumption, .inr (by assumption)⟩
  · exact ⟨_, by assumption, .inl (by assumption)⟩
```

---

## 4. Goal-list & VCGen utilities

### `combine_n N`
Source: [Tactics/Hoist.lean:3](../Flex/Tactic/Tactics/Hoist.lean#L3). Combines the first `N` goals into a single conjunctive goal; reassembles the original `N` proofs via `And.left`/`And.right`.

```lean
example : True ∧ True ∧ True := by
  refine ⟨?_, ?_, ?_⟩
  combine_n 3
  exact ⟨trivial, trivial, trivial⟩
```

### `simp_scopes`
Source: [VCG/While/Tactics.lean:14](../Flex/VCG/While/Tactics.lean#L14). Normalizes every `List.eraseDups …` subterm in the goal via `whnf`. Used in the while-language VCGen to canonicalize scope lists without firing the full simp set.

```lean
example : List.eraseDups [1, 2, 1, 3] = [2, 1, 3] := by
  simp_scopes; rfl
```

---

## Suggested composition order for a typical VC

```lean
example : <some VC with ∃ κ, … > := by
  rewriteKs          -- 1. canonical κ-order
  solve_fixpoint     -- 2. zap + PA; may leave residual κ-goals
  -- residuals (if any): zap / split_hyps / leafClosers
```

When only acyclic κ's are present, prefer `zap`. When you want a single κ as a named `let`, use `solK1`.
