import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BasicsTestAbs
open Classical
set_option linter.unusedVariables false


namespace F

namespace BasicsTestAbsQualifs

@[qualif]
def EqTrue (x₀ : Prop) : Prop :=
  x₀

@[qualif]
def EqFalse (x₀ : Prop) : Prop :=
  (¬x₀)

@[qualif]
def EqZero (x₀ : Int) : Prop :=
  (x₀ = 0)

@[qualif]
def GtZero (x₀ : Int) : Prop :=
  (x₀ > 0)

@[qualif]
def GeZero (x₀ : Int) : Prop :=
  (x₀ ≥ 0)

@[qualif]
def LtZero (x₀ : Int) : Prop :=
  (x₀ < 0)

@[qualif]
def LeZero (x₀ : Int) : Prop :=
  (x₀ ≤ 0)

@[qualif]
def Eq (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ = y₀)

@[qualif]
def Gt (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ > y₀)

@[qualif]
def Ge (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ ≥ y₀)

@[qualif]
def Lt (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ < y₀)

@[qualif]
def Le (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ ≤ y₀)

@[qualif]
def Le1 (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ ≤ (y₀ - 1))

end BasicsTestAbsQualifs

open BasicsTestAbsQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def BasicsTestAbs_proof : BasicsTestAbs := by
  unfold BasicsTestAbs
  (try zap) ; (try benchSimpStar) ; (try solve)

end F
