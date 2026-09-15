import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RuntimeImpl__0__ReadU32
open Classical
set_option linter.unusedVariables false


namespace F

namespace RuntimeImpl0ReadU32Qualifs

@[qualif]
def EqTrue (cnt₀ : Prop) : Prop :=
  cnt₀

@[qualif]
def EqFalse (cnt₀ : Prop) : Prop :=
  (¬cnt₀)

@[qualif]
def EqZero (cnt₀ : Int) : Prop :=
  (cnt₀ = 0)

@[qualif]
def GtZero (cnt₀ : Int) : Prop :=
  (cnt₀ > 0)

@[qualif]
def GeZero (cnt₀ : Int) : Prop :=
  (cnt₀ ≥ 0)

@[qualif]
def LtZero (cnt₀ : Int) : Prop :=
  (cnt₀ < 0)

@[qualif]
def LeZero (cnt₀ : Int) : Prop :=
  (cnt₀ ≤ 0)

@[qualif]
def Eq (cnt₀ : Int) (self₀ : Int) : Prop :=
  (cnt₀ = self₀)

@[qualif]
def Gt (cnt₀ : Int) (self₀ : Int) : Prop :=
  (cnt₀ > self₀)

@[qualif]
def Ge (cnt₀ : Int) (self₀ : Int) : Prop :=
  (cnt₀ ≥ self₀)

@[qualif]
def Lt (cnt₀ : Int) (self₀ : Int) : Prop :=
  (cnt₀ < self₀)

@[qualif]
def Le (cnt₀ : Int) (self₀ : Int) : Prop :=
  (cnt₀ ≤ self₀)

@[qualif]
def Le1 (cnt₀ : Int) (self₀ : Int) : Prop :=
  (cnt₀ ≤ (self₀ - 1))

end RuntimeImpl0ReadU32Qualifs

open RuntimeImpl0ReadU32Qualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def RuntimeImpl__0__ReadU32_proof : RuntimeImpl__0__ReadU32 := by
  unfold RuntimeImpl__0__ReadU32
  (try zap) ; (try benchSimpStar) ; (try solve)

end F
