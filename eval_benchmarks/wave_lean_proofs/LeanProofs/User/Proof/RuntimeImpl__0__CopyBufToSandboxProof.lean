import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RuntimeImpl__0__CopyBufToSandbox
open Classical
set_option linter.unusedVariables false


namespace F

namespace RuntimeImpl0CopyBufToSandboxQualifs

@[qualif]
def EqTrue (n₀ : Prop) : Prop :=
  n₀

@[qualif]
def EqFalse (n₀ : Prop) : Prop :=
  (¬n₀)

@[qualif]
def EqZero (n₀ : Int) : Prop :=
  (n₀ = 0)

@[qualif]
def GtZero (n₀ : Int) : Prop :=
  (n₀ > 0)

@[qualif]
def GeZero (n₀ : Int) : Prop :=
  (n₀ ≥ 0)

@[qualif]
def LtZero (n₀ : Int) : Prop :=
  (n₀ < 0)

@[qualif]
def LeZero (n₀ : Int) : Prop :=
  (n₀ ≤ 0)

@[qualif]
def Eq (n₀ : Int) (src₀ : Int) : Prop :=
  (n₀ = src₀)

@[qualif]
def Gt (n₀ : Int) (src₀ : Int) : Prop :=
  (n₀ > src₀)

@[qualif]
def Ge (n₀ : Int) (src₀ : Int) : Prop :=
  (n₀ ≥ src₀)

@[qualif]
def Lt (n₀ : Int) (src₀ : Int) : Prop :=
  (n₀ < src₀)

@[qualif]
def Le (n₀ : Int) (src₀ : Int) : Prop :=
  (n₀ ≤ src₀)

@[qualif]
def Le1 (n₀ : Int) (src₀ : Int) : Prop :=
  (n₀ ≤ (src₀ - 1))

end RuntimeImpl0CopyBufToSandboxQualifs

open RuntimeImpl0CopyBufToSandboxQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def RuntimeImpl__0__CopyBufToSandbox_proof : RuntimeImpl__0__CopyBufToSandbox := by
  unfold RuntimeImpl__0__CopyBufToSandbox
  (try zap) ; (try benchSimpStar) ; (try solve)

end F
