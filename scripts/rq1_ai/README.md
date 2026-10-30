# RQ1: Original vs. Zap vs. Zap + Fix

Exactly 61 invariant-bearing VCs; no Wave or flux-medium. Each trial starts from
the same generated VC and specification dependencies. Existing proof modules,
handwritten witnesses, and case-specific proof helpers are not copied.

| Condition | Exact preparation after unfolding the VC |
|---|---|
| Original | No tactic |
| Zap | `flex (backends := [])` |
| Zap + Fix | `flex (backends := [fix])` |

Both tactic conditions retain the same default preprocessing, cleanup, and
residual discharger. Nesting is off. Fix uses deep scraping, the qualifier bank,
and batched SMT synthesis. Spacer/Eldarica are disabled. These labels describe
controlled configurations of the Flex portfolio, not literal `zap; fix` scripts.

## Prepare once

From the Flex root, with its dependencies already installed:

```sh
python3 scripts/rq1_ai/prepare.py --output /absolute/path/to/rq1-ai
uv venv /absolute/path/to/rq1-ai/runtime --python 3.10
uv pip install --python /absolute/path/to/rq1-ai/runtime/bin/python \
  -r scripts/rq1_ai/requirements.txt
```

Preparation builds only specification dependencies and the small experiment
support module. It does not execute all 183 tactic prefixes or any AI trials.
The manifest records source hashes, dependency pins, the classification, and a
randomized schedule of three repetitions. It rejects changes to frozen inputs.
Pin the AI model/version and reasoning setting before running that schedule;
the setup does not choose or launch a model.

## Start one trial

Start the server before giving the task to the AI. It opens one file and runs
its prefix once. Wait for `trials/SUITE/NAME/ARM/REPEAT/ready.json` before attaching
the agent. The server holds a macOS `caffeinate` assertion while alive.

```sh
/absolute/path/to/rq1-ai/runtime/bin/python scripts/rq1_ai/serve.py \
  --manifest /absolute/path/to/rq1-ai/experiment.json \
  --case cstr/GhostGPtrStrlen --arm zap_fix --repeat 1 \
  --transport streamable-http --port 8765
```

Attach an MCP client using:

```json
{"mcpServers":{"rq1-proof":{"url":"http://127.0.0.1:8765/mcp"}}}
```

The prepared directory also contains this `mcp.json` and a shorter launcher:
`start-trial.sh cstr/GhostGPtrStrlen zap_fix 1`.

Supply **only [AI.md](AI.md)** as the task guide and these six tools: `task`,
`edit_proof`, `check`, `goals`, `read_source`, `search_source`. Disable the agent's
shell, web, other connectors, repository search, and persistent memory. Start a
fresh conversation for every task/condition/repetition. Do not hand the agent
this operator README, experiment results, or completed proofs.

The tools expose only the assigned VC's specification sources and the editable
proof suffix. This is an evaluation interface, not an OS security sandbox for
malicious Lean metaprograms. Use a container/VM if running untrusted agents.

If `automatic` is true, record success without an AI call. Otherwise use the
same model and **16,000-token / 30-minute** agent budget in every condition.
The completed five- and 25-case pilot used 15 minutes; keep those results labelled
with their original budget. `pilot.py --agent-seconds 1800` sets the new budget
in the frozen manifest, including when reusing older prepared dependencies.
The external agent runner must enforce token usage and log model parameters;
the MCP service enforces its wall-time budget between calls. A Lean check has a
600-second diagnostic wait cap. Initial preparation uses the portfolio's
180-second cooperative deadline, including a 60-second PA budget. Record any
overrun; cooperative limits are not hard process deadlines.

## Avoid repeated builds

Keep the server and the opened task alive. `edit_proof` sends a ranged LSP edit
only after the frozen prefix. Do not run `lake build` between attempts. A cached
`.olean` for a file containing `flex; sorry` would not preserve its tactic state
after editing; the live Lean session does.

`events.jsonl` records actual prefix executions. A restart or invalidation must
be counted, not hidden. Dependency builds are shared and timed before trials;
prefix time is charged once per trial. Final proof elaboration is checked in
Lean, and `rq1_verify` rejects any axiom other than `propext`, `Classical.choice`,
and `Quot.sound`. The provided `sorry` placeholder never earns success.

Before a large run, validate the setup with:

```sh
/absolute/path/to/rq1-ai/runtime/bin/python scripts/rq1_ai/smoke.py \
  --manifest /absolute/path/to/rq1-ai/experiment.json
```

This checks a real VC in all three conditions and a second automatically
closed case. It verifies that suffix edits reuse preparation, admissions do
not close outstanding goals, and completed proofs are accepted.

## Record and compare

`pilot.py` records each model response's provider-reported token counts through
a local-only OpenTelemetry collector. `usage-events.jsonl` is flushed to disk
before acknowledgement; `usage.json` contains the running totals. Auxiliary
connection-warmup counts are kept separately. Successful runs must reconcile
with Codex's final usage or the runner stops with an accounting error.

At the wall limit, the runner interrupts Codex gracefully before terminating it.
Already recorded counts survive interruption. An interrupted model response may
have no final provider usage: its record is explicitly partial, never zero or a
claimed exact total. Reports must separate complete, partial, and unknown usage.
`usage_available` means some counts exist; `usage_complete` means the full total
was verified. Do not compare sums over different sets of complete records.

Each trial saves `Task.lean`, `events.jsonl`, and `status.json`. Collect agent
tokens, full AI wall time, and model details from the agent runner alongside
them; `tool_session_seconds` starts at the first tool call, not the first model
token. Compare:

- Automatic closures and additional AI completions, both out of the same 61.
- Paired per-VC outcomes across repetitions; retain failures and timeouts.
- AI tokens, edits, Lean-check time, and residual-proof time.
- Preparation time plus AI wall time, including every prefix rerun.
- Manually supplied predicate witnesses in completed proofs, audited afterward.

Use the fixed AI budget to compare residual-proof assistance. Also report
end-to-end completion curves at common total budgets, charging preparation.
Report acyclic-only, mixed, and cyclic-only strata using the frozen inventory;
do not guess a denominator from previous chat counts. This setup measures
assistance under a warm development workflow, not cold dependency installation.

Stop the trial server when finished; its exit cleanup terminates Lean and
releases `caffeinate`. Do not run multiple memory-intensive trials concurrently
on the same laptop. Smoke runs and setup measurements are not AI results.
