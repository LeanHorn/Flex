import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RuntimeImpl__0__WriteU8
open Classical
set_option linter.unusedVariables false


namespace F

namespace RuntimeImpl0WriteU8Qualifs

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
def Eq (cnt₀ : Int) (v₀ : Int) : Prop :=
  (cnt₀ = v₀)

@[qualif]
def Gt (cnt₀ : Int) (v₀ : Int) : Prop :=
  (cnt₀ > v₀)

@[qualif]
def Ge (cnt₀ : Int) (v₀ : Int) : Prop :=
  (cnt₀ ≥ v₀)

@[qualif]
def Lt (cnt₀ : Int) (v₀ : Int) : Prop :=
  (cnt₀ < v₀)

@[qualif]
def Le (cnt₀ : Int) (v₀ : Int) : Prop :=
  (cnt₀ ≤ v₀)

@[qualif]
def Le1 (cnt₀ : Int) (v₀ : Int) : Prop :=
  (cnt₀ ≤ (v₀ - 1))

end RuntimeImpl0WriteU8Qualifs

open RuntimeImpl0WriteU8Qualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def RuntimeImpl__0__WriteU8_proof : RuntimeImpl__0__WriteU8 := by
  unfold RuntimeImpl__0__WriteU8
  (try zap) ; (try benchSimpStar) ; (try solve)

end F
