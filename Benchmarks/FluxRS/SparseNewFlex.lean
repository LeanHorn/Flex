import Benchmarks.FluxRS.«sparse-new»

/-! Sparse-vector construction through the unified `flex` tactic. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem SparseNew_flex : F.SparseImpl__0__New := by
  flex

#print axioms SparseNew_flex
