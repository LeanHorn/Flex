# Your Lean proof task

Complete the assigned theorem. Use only this guide and the supplied experiment
tools. Do not browse repositories, Git history, the web, other cases, or previous
solutions. Read the assigned VC and its definitions through `read_source` and
`search_source` when needed. The task statement and definitions are fixed.

## Working on the proof

1. Call `task` to see the current proof, remaining goals, and available sources.
2. Submit a complete replacement for the editable tactic block with `edit_proof`.
   Do not include `by` or repeat the frozen prefix. Put helper arguments and
   lemmas inside the proof using `have`, `let`, or local induction.
3. Use `goals` to inspect a position in your proof. Lines and columns are
   one-based. `check` returns current diagnostics; it does not rebuild the project.
4. Finish when the tool reports `complete: true`. A file containing admitted
   goals is not a success. Never use `sorry`, `admit`, new axioms, or trusted SMT
   evidence in the submitted solution.

Keep one tool session open. It preserves Lean's elaborated prefix when you edit
the proof below it. Do not run `lake build`, restart the server, or edit imports,
options, definitions, or the prefix. The preparation cost is recorded separately.

## What the prefix has done

The condition is fixed by the experiment; do not invoke additional invariant
synthesis tactics (`flex`, `zap`, `fix`, `spacer`, `eldarica`, `solve`, or
`solve_fixpoint`) in the editable block.

| Condition | Frozen preparation |
|---|---|
| Original | Unfold the VC; no synthesis |
| Zap | Flex preprocessing, Zap elimination, cleanup, and residual discharge; no synthesis backends |
| Zap + Fix | The same pipeline, with Fix as the only additional backend |

Zap constructs witnesses for predicates selected for acyclic elimination. Fix
uses predicate abstraction with the standard qualifier bank and deep scraping.
Both can leave proof obligations. If existential predicates remain, you may
provide their witnesses manually with `refine ⟨..., ?_⟩`. Do not assume all
predicates were eliminated or that every remaining goal is arithmetic.

The final two conditions include the same residual automation. Fix candidates
must pass its head and safety checks; solver validation can still leave a Lean
proof obligation. Spacer/Eldarica are disabled in this experiment.

## Completing a residual

Read the actual goal before choosing a tactic. Typical steps are `intro`,
`constructor`, `rcases`, `subst`, `simp`, `omega`, `grind`, and `aesop`. Use the
provided definitions and lemmas for arrays, strings, lists, and recursive
functions; arithmetic automation cannot invent their semantics.

`flex_discharge` is allowed: it attempts checked SMT/native proof automation
without synthesizing predicates. `flex_smt` is also available for reconstructed
SMT proofs. Do not use `flex_auto`, whose trusted SMT mode is not acceptable as
final evidence. The final checker rejects admissions and unexpected axioms.

If a proof attempt fails, inspect its diagnostics and revise the editable block.
Do not replace the theorem statement, change the preparation, or hide failures.
