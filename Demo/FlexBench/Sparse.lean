import Flex.Tactic.Tactics.Flex
import Benchmarks.FluxRS.«sparse-new»

/-! A sparse-vector constructor: `fix` runs out of its heartbeat share and is
rolled back; `spacer` then finds the invariants and the closer finishes. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem SparseNew_flex : F.SparseImpl__0__New := by
  flex

#print axioms SparseNew_flex
