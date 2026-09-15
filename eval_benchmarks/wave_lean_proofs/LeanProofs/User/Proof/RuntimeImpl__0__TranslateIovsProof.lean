import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RuntimeImpl__0__TranslateIovs
open Classical
set_option linter.unusedVariables false


namespace F

namespace RuntimeImpl0TranslateIovsQualifs

@[qualif]
def MyQ1 (a'₉ : Int) (a'₁₀ : Int) (a'₁₁ : Int) : Prop :=
  ((a'₉ + a'₁₀) ≤ (a'₁₁ + types_LINEAR_MEM_SIZE))

@[qualif]
def EqTrue (iovs₀ : Prop) : Prop :=
  iovs₀

@[qualif]
def EqFalse (iovs₀ : Prop) : Prop :=
  (¬iovs₀)

@[qualif]
def EqZero (iovs₀ : Int) : Prop :=
  (iovs₀ = 0)

@[qualif]
def GtZero (iovs₀ : Int) : Prop :=
  (iovs₀ > 0)

@[qualif]
def GeZero (iovs₀ : Int) : Prop :=
  (iovs₀ ≥ 0)

@[qualif]
def LtZero (iovs₀ : Int) : Prop :=
  (iovs₀ < 0)

@[qualif]
def LeZero (iovs₀ : Int) : Prop :=
  (iovs₀ ≤ 0)

@[qualif]
def Eq (iovs₀ : Int) (idx₀ : Int) : Prop :=
  (iovs₀ = idx₀)

@[qualif]
def Gt (iovs₀ : Int) (idx₀ : Int) : Prop :=
  (iovs₀ > idx₀)

@[qualif]
def Ge (iovs₀ : Int) (idx₀ : Int) : Prop :=
  (iovs₀ ≥ idx₀)

@[qualif]
def Lt (iovs₀ : Int) (idx₀ : Int) : Prop :=
  (iovs₀ < idx₀)

@[qualif]
def Le (iovs₀ : Int) (idx₀ : Int) : Prop :=
  (iovs₀ ≤ idx₀)

@[qualif]
def Le1 (iovs₀ : Int) (idx₀ : Int) : Prop :=
  (iovs₀ ≤ (idx₀ - 1))

end RuntimeImpl0TranslateIovsQualifs

open RuntimeImpl0TranslateIovsQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def RuntimeImpl__0__TranslateIovs_proof : RuntimeImpl__0__TranslateIovs := by
  unfold RuntimeImpl__0__TranslateIovs
  (try zap) ; (try benchSimpStar) ; (try solve)

end F
