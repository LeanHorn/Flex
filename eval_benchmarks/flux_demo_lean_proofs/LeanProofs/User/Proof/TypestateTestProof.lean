import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TypestateTest
open Classical
set_option linter.unusedVariables false


namespace F

namespace TypestateTestQualifs

@[qualif]
def EqTrue (pin₀ : Prop) : Prop :=
  pin₀

@[qualif]
def EqFalse (pin₀ : Prop) : Prop :=
  (¬pin₀)

@[qualif]
def EqZero (pin₀ : Int) : Prop :=
  (pin₀ = 0)

@[qualif]
def GtZero (pin₀ : Int) : Prop :=
  (pin₀ > 0)

@[qualif]
def GeZero (pin₀ : Int) : Prop :=
  (pin₀ ≥ 0)

@[qualif]
def LtZero (pin₀ : Int) : Prop :=
  (pin₀ < 0)

@[qualif]
def LeZero (pin₀ : Int) : Prop :=
  (pin₀ ≤ 0)

@[qualif]
def Eq (pin₀ : Int) (v₀ : Int) : Prop :=
  (pin₀ = v₀)

@[qualif]
def Gt (pin₀ : Int) (v₀ : Int) : Prop :=
  (pin₀ > v₀)

@[qualif]
def Ge (pin₀ : Int) (v₀ : Int) : Prop :=
  (pin₀ ≥ v₀)

@[qualif]
def Lt (pin₀ : Int) (v₀ : Int) : Prop :=
  (pin₀ < v₀)

@[qualif]
def Le (pin₀ : Int) (v₀ : Int) : Prop :=
  (pin₀ ≤ v₀)

@[qualif]
def Le1 (pin₀ : Int) (v₀ : Int) : Prop :=
  (pin₀ ≤ (v₀ - 1))

end TypestateTestQualifs

open TypestateTestQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def TypestateTest_proof : TypestateTest := by
  unfold TypestateTest
  (try zap) ; (try benchSimpStar) ; (try solve)

end F
