import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.KmeansMinIndex
open Classical
set_option linter.unusedVariables false


namespace F

namespace KmeansMinIndexQualifs

@[qualif]
def EqTrue (min₀ : Prop) : Prop :=
  min₀

@[qualif]
def EqFalse (min₀ : Prop) : Prop :=
  (¬min₀)

@[qualif]
def EqZero (min₀ : Int) : Prop :=
  (min₀ = 0)

@[qualif]
def GtZero (min₀ : Int) : Prop :=
  (min₀ > 0)

@[qualif]
def GeZero (min₀ : Int) : Prop :=
  (min₀ ≥ 0)

@[qualif]
def LtZero (min₀ : Int) : Prop :=
  (min₀ < 0)

@[qualif]
def LeZero (min₀ : Int) : Prop :=
  (min₀ ≤ 0)

@[qualif]
def Eq (min₀ : Int) (iter₀ : Int) : Prop :=
  (min₀ = iter₀)

@[qualif]
def Gt (min₀ : Int) (iter₀ : Int) : Prop :=
  (min₀ > iter₀)

@[qualif]
def Ge (min₀ : Int) (iter₀ : Int) : Prop :=
  (min₀ ≥ iter₀)

@[qualif]
def Lt (min₀ : Int) (iter₀ : Int) : Prop :=
  (min₀ < iter₀)

@[qualif]
def Le (min₀ : Int) (iter₀ : Int) : Prop :=
  (min₀ ≤ iter₀)

@[qualif]
def Le1 (min₀ : Int) (iter₀ : Int) : Prop :=
  (min₀ ≤ (iter₀ - 1))

end KmeansMinIndexQualifs

open KmeansMinIndexQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def KmeansMinIndex_proof : KmeansMinIndex := by
  unfold KmeansMinIndex
  (try zap) ; (try benchSimpStar) ; (try solve)

end F
