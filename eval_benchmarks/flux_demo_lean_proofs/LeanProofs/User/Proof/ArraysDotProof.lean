import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.ArraysDot
open Classical
set_option linter.unusedVariables false


namespace F

namespace ArraysDotQualifs

@[qualif]
def EqTrue (iter₀ : Prop) : Prop :=
  iter₀

@[qualif]
def EqFalse (iter₀ : Prop) : Prop :=
  (¬iter₀)

@[qualif]
def EqZero (iter₀ : Int) : Prop :=
  (iter₀ = 0)

@[qualif]
def GtZero (iter₀ : Int) : Prop :=
  (iter₀ > 0)

@[qualif]
def GeZero (iter₀ : Int) : Prop :=
  (iter₀ ≥ 0)

@[qualif]
def LtZero (iter₀ : Int) : Prop :=
  (iter₀ < 0)

@[qualif]
def LeZero (iter₀ : Int) : Prop :=
  (iter₀ ≤ 0)

@[qualif]
def Eq (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ = r₀)

@[qualif]
def Gt (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ > r₀)

@[qualif]
def Ge (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ ≥ r₀)

@[qualif]
def Lt (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ < r₀)

@[qualif]
def Le (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ ≤ r₀)

@[qualif]
def Le1 (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ ≤ (r₀ - 1))

end ArraysDotQualifs

open ArraysDotQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def ArraysDot_proof : ArraysDot := by
  unfold ArraysDot
  (try zap) ; (try benchSimpStar) ; (try solve)

end F
